// Fixture R4 (issue #48, step 3, abort signal). Two runs fetch a local
// server that answers after 10 s: W passes its AbortSignal to fetch, I
// ignores it. Both lose a race to a short sleep; the handler, standing
// in for the executor, then aborts both signals, keeps both runs in the
// race until they settle, and logs a warning for any run not settled
// within the grace period after its abort.
//
// SDK 1.18.4 calls a run's action with no arguments (RunAction is
// `() => Promise<T>`; context_impl.js calls `action()`), so the SDK has
// no per-run signal. As restate-sdk-gen does (fiber.ts runController),
// the emulated executor owns one AbortController per run and hands its
// signal to the closure.
import { noteAttempt, event, tag, tick, effect } from "./lib.mjs";

const slowUrl = `http://127.0.0.1:${process.env.SLOW_PORT ?? 19934}/slow`;
const graceMs = 2000;

// The closure's work: fetch the slow server, with or without a signal.
const fetchSlow = (label, signal) => async () => {
  const response = await fetch(slowUrl, {
    headers: { "x-run": label }, signal
  });
  return response.text();
};

// Wraps a closure as the executor would: logs start and settle, and,
// when `convert` is on, turns a rejection caused by the abort into a
// TerminalError (restate-sdk-gen restate-operations.ts:163-176).
const guarded = (ctx, sdk, convert, controller, label, work) => async () => {
  effect(ctx, label);
  event(ctx, `${label}-start`);
  try {
    const value = await work();
    event(ctx, `${label}-settle`, "ok");
    return value;
  } catch (error) {
    event(ctx, `${label}-settle`, error.name);
    const aborted = convert && controller.signal.aborted;
    if (aborted) throw new sdk.TerminalError(`aborted: ${error.name}`);
    throw error;
  }
};

// Aborts one run's signal and arms its grace-period warning.
const abortWithGrace = (ctx, controller, label, settled) => {
  event(ctx, `abort-${label}`);
  controller.abort();
  setTimeout(() => {
    if (!settled.has(label)) event(ctx, `WARN-unsettled-${label}`, graceMs);
  }, graceMs);
};

const labelOf = (winner) => winner.split("!")[0];

// R4: `convert` off is control A, `abort` off is control B.
const abortLoser = (sdk, convert, abort) => async (ctx) => {
  noteAttempt(ctx, `r4-${convert}-${abort}`);
  const { race } = sdk.RestatePromise;
  const controllers = new Map([["w", new AbortController()],
    ["i", new AbortController()]]);
  const workOf = (label, c) =>
    fetchSlow(label, label === "w" ? c.signal : undefined);
  const runs = new Map([...controllers].map(([label, c]) => [label,
    tag(label)(ctx.run(label,
      guarded(ctx, sdk, convert, c, label, workOf(label, c))))]));
  await tick(ctx, "first", race([...runs.values(),
    tag("s")(ctx.sleep(100))]));
  const settled = new Set();
  event(ctx, "abort-point");
  if (abort) controllers.forEach((c, l) => abortWithGrace(ctx, c, l, settled));
  while (runs.size > 0) {
    const winner = labelOf(await tick(ctx, "race", race([...runs.values()])));
    runs.delete(winner);
    settled.add(winner);
  }
  return "done";
};

/** R4 handlers, keyed by handler name. */
export const abortHandlers = (sdk) => ({
  r4: abortLoser(sdk, true, true),
  r4NoConvert: abortLoser(sdk, false, true),
  r4NoAbort: abortLoser(sdk, true, false)
});
