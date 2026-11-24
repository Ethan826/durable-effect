// Fixture R5 (issue #48, step 3, rule 1 mitigation "re-abort"): a run
// that an earlier attempt aborted is aborted again at once when a later
// attempt executes it again.
//
// Run r honours its signal slowly: on abort it takes 3 s to wind down.
// It loses a race to a short sleep, the emulated executor aborts it,
// and the service's abort timeout (1 s after a 200 ms inactivity
// timeout) ends attempt 1 before r settles, so r has no journaled
// result. Attempt 2 replays the lost race and executes r again.
//
// Main: the executor owns one AbortController per run, made when the
// run is issued and aborted at the fiber's interruption. Control: the
// controller is made when the closure starts, and the interruption
// aborts whichever controller exists then; on replay none may exist
// yet, so r runs unaborted and every attempt repeats it.
import { noteAttempt, event, tag, tick, effect } from "../runs/lib.mjs";

const workMs = 10_000;
const windDownMs = 3_000;

const abortError = (why) =>
  Object.assign(new Error(`aborted ${why}`), { name: "AbortError" });

// r's work: 10 s, or a 3 s wind-down after an abort, or an immediate
// rejection when the signal is already aborted (as fetch does).
const slowHonour = (signal) => new Promise((resolve, reject) => {
  if (signal.aborted) return reject(abortError("at-start"));
  const done = setTimeout(() => resolve("r-ok"), workMs);
  const windDown = () => {
    clearTimeout(done);
    setTimeout(() => reject(abortError("wound-down")), windDownMs);
  };
  signal.addEventListener("abort", windDown, { once: true });
});

// The executor's wrapper: logs, counts the work as an external effect
// only when it starts unaborted, and makes an abort terminal.
const guarded = (ctx, sdk, signalOf) => async () => {
  const signal = signalOf();
  event(ctx, "r-start", signal.aborted ? "aborted" : "live");
  if (!signal.aborted) effect(ctx, "r");
  try {
    const value = await slowHonour(signal);
    event(ctx, "r-settle", "ok");
    return value;
  } catch (error) {
    event(ctx, "r-settle", error.message.replace(" ", "-"));
    if (signal.aborted) throw new sdk.TerminalError(error.message);
    throw error;
  }
};

const labelOf = (winner) => winner.split("!")[0];

// `carry` on: controller per run (main). Off: per closure (control).
const rerun = (sdk, carry) => async (ctx) => {
  noteAttempt(ctx, carry ? "r5" : "r5Fresh");
  const { race } = sdk.RestatePromise;
  let current = carry ? new AbortController() : undefined;
  const signalOf = () => {
    if (!carry) current = new AbortController();
    return current.signal;
  };
  const run = tag("r")(ctx.run("r", guarded(ctx, sdk, signalOf)));
  const first = await tick(ctx, "first",
    race([run, tag("s")(ctx.sleep(100))]));
  if (labelOf(first) === "r") return "r-won";
  event(ctx, "abort-point", current === undefined ? "none" : "abort");
  current?.abort();
  await tick(ctx, "close", race([run]));
  return "done";
};

/** R5 handlers, keyed by handler name. */
export const rerunHandlers = (sdk) => ({
  r5: rerun(sdk, true),
  r5Fresh: rerun(sdk, false)
});

/** R5's service options: attempt 1 ends 1 s after inactivity. */
export const rerunOptions = {
  journalRetention: 3600_000, inactivityTimeout: 200, abortTimeout: 1000
};
