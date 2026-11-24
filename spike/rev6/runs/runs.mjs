// Fixtures R1 to R3 (issue #48, step 3, side effects of ctx.run). The
// executor does not exist yet, so each handler emulates one executor
// rule with a fresh RestatePromise.race per tick:
//   R1, an executing run is never dropped: it stays in every later race
//       until it settles, and its result is delivered to no one;
//   R2, closing waits for executing runs;
//   R3, a run's retryable failure is held until its siblings settle.
// Each variant flag switches the rule off for the control.
import { noteAttempt, event, tag, tick, pause, effect } from "./lib.mjs";

// A run that records its effect, takes `ms`, logs when it settles and
// then calls `onSettle`.
const timedRun = (ctx, key, ms, onSettle = () => {}) =>
  tag(key)(ctx.run(key, async () => {
    effect(ctx, key);
    event(ctx, `${key}-start`);
    await pause(ms);
    event(ctx, `${key}-settle`, "ok");
    onSettle();
    return `${key}-ok`;
  }));

const labelOf = (winner) => winner.split("!")[0];

// Races `member` beside every kept run until `member` wins. A kept run
// that wins first leaves the set; its result goes to no one.
const awaitKeeping = async (ctx, race, kept, label, member) => {
  const next = () => tick(ctx, label, race([...kept.values(), member]));
  let winner = await next();
  while (kept.has(labelOf(winner))) {
    kept.delete(labelOf(winner));
    winner = await next();
  }
  return winner;
};

// Races the kept runs until every one has settled.
const drainKept = async (ctx, race, kept, label) => {
  while (kept.size > 0) {
    kept.delete(labelOf(await tick(ctx, label, race([...kept.values()]))));
  }
};

// The durable work R1 does while the run executes: [label, make].
const otherWork = [
  ["s2", (ctx) => tag("s2")(ctx.sleep(200))],
  ["q", (ctx) => timedRun(ctx, "q", 10)],
  ["s3", (ctx) => tag("s3")(ctx.sleep(300))]
];

// R1: the run loses to a sleep; it is kept (or, as control, dropped).
const neverDropped = (race, keep) => async (ctx) => {
  noteAttempt(ctx, keep ? "r1Keep" : "r1Drop");
  const run = timedRun(ctx, "r", 1500);
  await tick(ctx, "first", race([run, tag("s1")(ctx.sleep(100))]));
  const kept = new Map(keep ? [["r", run]] : []);
  for (const [label, make] of otherWork) {
    event(ctx, `issue-${label}`);
    await awaitKeeping(ctx, race, kept, label, make(ctx));
  }
  await drainKept(ctx, race, kept, "close");
  return "done";
};

// R2: closing races the executing run until it settles (control: not).
const closingWaits = (race, wait) => async (ctx) => {
  noteAttempt(ctx, wait ? "r2Wait" : "r2Return");
  const run = timedRun(ctx, "r", 1500);
  await tick(ctx, "first", race([run, tag("s1")(ctx.sleep(100))]));
  if (wait) await tick(ctx, "close", race([run]));
  event(ctx, "return");
  return "done";
};

// R3's failing run: throws in attempt 1 only. When `held`, its
// rejection waits until the handler releases it (A has settled).
const failingRun = (ctx, n, held) => tag("b")(ctx.run("b", async () => {
  effect(ctx, "b");
  await pause(100);
  event(ctx, "b-fail-ready");
  if (n !== 1) return "b-ok";
  await held;
  event(ctx, "b-reject");
  throw new Error("b fails in attempt 1");
}));

// R3: B's failure is held until A has settled (control: not held).
// `hold` is "delivered" (A's result reached the handler through a race),
// "settled" (A's closure returned) or "none" (the control).
const failureHeld = (race, hold) => async (ctx) => {
  const n = noteAttempt(ctx, `r3-${hold}`);
  let release = () => {};
  const held = hold === "none" ? undefined :
    new Promise((r) => { release = r; });
  const onSettle = hold === "settled" ? () => release() : undefined;
  const runs = new Map([["a", timedRun(ctx, "a", 1000, onSettle)],
    ["b", failingRun(ctx, n, held)]]);
  while (runs.size > 0) {
    const winner = labelOf(await tick(ctx, "race", race([...runs.values()])));
    runs.delete(winner);
    if (winner === "a" && hold === "delivered") release();
  }
  return "done";
};

/** R1 to R3 handlers, keyed by handler name. */
export const runHandlers = (sdk) => {
  const { race } = sdk.RestatePromise;
  return {
    r1Keep: neverDropped(race, true), r1Drop: neverDropped(race, false),
    r2Wait: closingWaits(race, true), r2Return: closingWaits(race, false),
    r3Hold: failureHeld(race, "delivered"),
    r3HoldSettled: failureHeld(race, "settled"),
    r3NoHold: failureHeld(race, "none")
  };
};
