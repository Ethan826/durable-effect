// Fixtures O1 to O3 (issue #48, step 7): the three open items of the
// adversarial review of revision 6 (comment 7144035354). Each handler
// emulates one executor rule by hand; check.mjs decides from the
// journals, the SDK log and the effects file.
//
// O1. A cancel signal is handled in journal order on replay (A1): with
//     sleeps s1 and s2 pending and a cancel journaled between their
//     completions, every attempt sees s1, then the cancel, then s2.
//     s2 is 4 s, so the driver's cancel at 1 s lands between them; an
//     earlier run with s2 at 1.5 s once had its cancel arrive too late.
// O2. The entry gate (C24) when a sample's result is missing from the
//     journal: on replay a cancellation is consumed while the turn waits
//     for a fresh sample, and run r is raced beside that sample.
//     Main: r's wrapper waits until the cancellation's turn has aborted
//     r, so r's work does not start again. Control: no gate.
// O3. Outcomes proposed before a retryable failure ends the attempt
//     (M2): run a settles after run b fails retryably. Main: b's failure
//     is held until a settles, and a's outcome is returned first.
//     Controls: b's failure returned at once (no freeze), or before a's
//     outcome (retryable first).
import { noteAttempt, attemptOf, event, tag, tick, pause, effect }
  from "../runs/lib.mjs";

const isCancel = (sdk, error) => error instanceof sdk.CancelledError;

// O1: one fresh race per tick over every pending sleep.
const o1 = (sdk) => async (ctx) => {
  noteAttempt(ctx, "o1");
  const { race } = sdk.RestatePromise;
  const pending = new Map([["s1", ctx.sleep(500, "s1")],
    ["s2", ctx.sleep(4000, "s2")]]);
  while (pending.size > 0) {
    const members = [...pending].map(([label, p]) => tag(label)(p));
    try {
      const winner = await tick(ctx, "o1", race(members));
      pending.delete(winner.split("!")[0]);
    } catch (error) {
      if (!isCancel(sdk, error)) throw error;
      event(ctx, "tick-o1", "cancel");
    }
  }
  return "o1-done";
};

const abortError = () =>
  Object.assign(new Error("aborted"), { name: "AbortError" });

// r's work: 5 s, or an immediate rejection once its signal aborts.
const honour = (signal) => new Promise((resolve, reject) => {
  if (signal.aborted) return reject(abortError());
  const done = setTimeout(() => resolve("r-ok"), 5_000);
  signal.addEventListener("abort", () => {
    clearTimeout(done);
    reject(abortError());
  }, { once: true });
});

// The executor's wrapper for r, with or without the entry gate.
// `gateState.barrier` is unresolved only while a consumed cause waits to
// be acted on; the wrapper reads it when the SDK starts the closure.
const gatedRun = (ctx, sdk, signal, gateState, gate) => async () => {
  if (gate) await gateState.barrier.promise;
  event(ctx, "r-start", signal.aborted ? "aborted" : "live");
  if (signal.aborted) throw new sdk.TerminalError("aborted-at-entry");
  effect(ctx, "r");
  try {
    return await honour(signal);
  } catch (error) {
    if (signal.aborted) throw new sdk.TerminalError("aborted");
    throw error;
  }
};

// The sample: slow in attempt 1, so the abort timeout ends that attempt
// before its result is journaled; quick afterwards.
const sample = (ctx) => async () => {
  await pause(attemptOf(ctx) === 1 ? 2_500 : 100);
  return Date.now();
};

// Awaits race([sample, r]) until the sample wins, counting cancels.
const awaitSample = async (ctx, sdk, members, gateState) => {
  let cancels = 0;
  for (;;) {
    try {
      const winner = await tick(ctx, "o2", sdk.RestatePromise.race(members));
      return { winner, cancels };
    } catch (error) {
      if (!isCancel(sdk, error)) throw error;
      cancels += 1;
      gateState.barrier = Promise.withResolvers();
      event(ctx, "tick-o2", "cancel");
    }
  }
};

const o2 = (sdk, gate) => async (ctx) => {
  noteAttempt(ctx, gate ? "o2Gate" : "o2NoGate");
  const controller = new AbortController();
  const settledBarrier = Promise.withResolvers();
  settledBarrier.resolve();
  const gateState = { barrier: settledBarrier };
  const r = tag("r")(ctx.run("r",
    gatedRun(ctx, sdk, controller.signal, gateState, gate)));
  await tick(ctx, "o2", sdk.RestatePromise.race([r, tag("s1")(ctx.sleep(300, "s1"))]));
  const s = tag("sample")(ctx.run("sample", sample(ctx)));
  const { winner, cancels } = await awaitSample(ctx, sdk, [s, r], gateState);
  if (cancels > 0) controller.abort();
  event(ctx, "caught-up", `${winner} cancels=${cancels}`);
  gateState.barrier.resolve();
  const last = await tick(ctx, "o2", sdk.RestatePromise.race([r]));
  return `o2-${last}`;
};

const fail = () => { throw new Error("b-retryable"); };
const nextTask = () => new Promise((resolve) => setImmediate(resolve));

// O3's two closures. `order` is "freeze" (main: b waits for a, a's
// outcome returned first), "noFreeze" (b fails at once) or
// "retryableFirst" (b waits for a, but b's failure is returned first).
const o3Runs = (ctx, sdk, aKind, order) => {
  const aSettled = Promise.withResolvers();
  const bReturned = Promise.withResolvers();
  const a = async () => {
    await pause(300);
    effect(ctx, "a");
    aSettled.resolve();
    if (order === "retryableFirst") { await bReturned.promise; await nextTask(); }
    if (aKind === "terminal") throw new sdk.TerminalError("a-terminal");
    return "a-ok";
  };
  const b = async () => {
    await pause(100);
    effect(ctx, "b");
    if (attemptOf(ctx) > 1) return "b-ok";
    if (order !== "noFreeze") await aSettled.promise;
    if (order === "freeze") await nextTask();
    bReturned.resolve();
    fail();
  };
  return { a, b };
};

const o3 = (sdk, aKind, order) => async (ctx) => {
  noteAttempt(ctx, `o3-${aKind}-${order}`);
  const { a, b } = o3Runs(ctx, sdk, aKind, order);
  const ra = tag("a")(ctx.run("a", a));
  const rb = tag("b")(ctx.run("b", b));
  const first = await tick(ctx, "o3", sdk.RestatePromise.race([ra, rb]));
  const second = await tick(ctx, "o3", sdk.RestatePromise.race(
    [first.startsWith("a") ? rb : ra]));
  return `o3-${first}-${second}`;
};

/** O1 to O3 handlers, keyed by handler name. */
export const openHandlers = (sdk) => ({
  o1: o1(sdk),
  o2Gate: o2(sdk, true),
  o2NoGate: o2(sdk, false),
  o3OkFreeze: o3(sdk, "ok", "freeze"),
  o3OkNoFreeze: o3(sdk, "ok", "noFreeze"),
  o3TermFreeze: o3(sdk, "terminal", "freeze"),
  o3TermRetryableFirst: o3(sdk, "terminal", "retryableFirst")
});

/** O1 forces a suspension and replay at every await. */
export const replayOptions = { journalRetention: 3600_000, inactivityTimeout: 200 };
/** O2's attempt 1 ends 0.8 s after inactivity, before its sample settles. */
export const gateOptions = {
  journalRetention: 3600_000, inactivityTimeout: 200, abortTimeout: 800
};
/** O3 runs live. */
export const liveOptions = { journalRetention: 3600_000 };
