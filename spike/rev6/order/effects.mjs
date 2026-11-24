// rev6-effects fixtures F17 to F19 (register on #48, A9, A10, A11).
// Each run records its side effect in the effects file, outside the
// journal, so check.mjs can count executions.
import {
  noteAttempt, tag, tick, pause, effect, retention, replayOptions
} from "./lib.mjs";

// F17: a dropped run is still executing when the attempt suspends.
const droppedAtSuspension = (race, keep) => async (ctx) => {
  noteAttempt(ctx, keep ? "f17Keep" : "f17");
  const run = tag("run")(ctx.run("effect", async () => {
    effect(ctx, "f17run");
    await pause(1500);
    return "ran";
  }));
  await tick(ctx, "first", race([run, tag("s1")(ctx.sleep(100))]));
  const later = tag("s2")(ctx.sleep(600));
  await tick(ctx, "second", race(keep ? [run, later] : [later]));
  if (keep) await tick(ctx, "third", race([run]));
  return "done";
};

// F18: when a run's action executes.
const countingRun = (ctx) => tag("run")(ctx.run("effect", async () => {
  effect(ctx, "f18run");
  return "ran";
}));
const unraced = (race) => async (ctx) => {
  noteAttempt(ctx, "f18Unraced");
  countingRun(ctx);
  await tick(ctx, "sleep", race([tag("s")(ctx.sleep(300))]));
  return "done";
};
// The short sleep's result is queued while the long one is awaited.
const besideQueued = (race) => async (ctx) => {
  noteAttempt(ctx, "f18Beside");
  const short = tag("short")(ctx.sleep(100));
  await tick(ctx, "long", race([tag("long")(ctx.sleep(800))]));
  const run = countingRun(ctx);
  await tick(ctx, "race", race([run, short]));
  return "done";
};
// The short sleep was itself the winner of an earlier race.
const besideTaken = (race) => async (ctx) => {
  noteAttempt(ctx, "f18BesideTaken");
  const short = tag("short")(ctx.sleep(100));
  await tick(ctx, "short", race([short]));
  const run = countingRun(ctx);
  await tick(ctx, "race", race([run, short]));
  return "done";
};
const alone = (race) => async (ctx) => {
  noteAttempt(ctx, "f18Alone");
  await tick(ctx, "race", race([countingRun(ctx)]));
  return "done";
};

// F19: one run fails retryably while another, slower, is in flight.
const concurrentFailure = (race, sdk, terminal) => async (ctx) => {
  const n = noteAttempt(ctx, terminal ? "f19Terminal" : "f19");
  const slow = tag("slow")(ctx.run("slow", async () => {
    effect(ctx, "f19slow");
    await pause(800);
    return 1;
  }));
  const bad = tag("bad")(ctx.run("bad", async () => {
    effect(ctx, "f19bad");
    await pause(100);
    if (terminal) throw new sdk.TerminalError("bad run");
    if (n === 1) throw new Error("retryable bad run");
    return "ok";
  }));
  await tick(ctx, "first", race([slow, bad]));
  await tick(ctx, "second", race([slow]));
  return "done";
};

/** Builds the rev6-effects services from the loaded SDK. */
export const effectServices = (sdk) => {
  const { race } = sdk.RestatePromise;
  const handlers = {
    f17: droppedAtSuspension(race, false),
    f17Keep: droppedAtSuspension(race, true),
    f18Unraced: unraced(race), f18Beside: besideQueued(race),
    f18BesideTaken: besideTaken(race), f18Alone: alone(race),
    f19: concurrentFailure(race, sdk, false),
    f19Terminal: concurrentFailure(race, sdk, true)
  };
  return [
    sdk.service({ name: "Effects", handlers, options: replayOptions }),
    sdk.service({ name: "EffectsLive", handlers, options: retention })
  ];
};
