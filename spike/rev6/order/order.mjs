// rev6-order fixtures F1 to F4, F9 and F10 (register on #48, A1, A2,
// A12, A14, A18, A23). Every wait is one fresh race over the operations
// still wanted, except where a fixture keeps a second polling loop alive
// on purpose (F3 and F4's controls).
import {
  noteAttempt, tag, tick, pause, effect, slicedTurn, invocationOf,
  retention, replayOptions
} from "./lib.mjs";

const liveWinner = new Map();
const noop = () => undefined;
const quickRun = (ctx, name) =>
  tag(name)(ctx.run(name, () => pause(20).then(() => name)));
const forceReplay = (ctx, race) =>
  tick(ctx, "force", race([tag("force")(ctx.sleep(400))]));

// F1: two runs whose results arrive together; force a replay.
const adjacent = (race, changed) => async (ctx) => {
  const n = noteAttempt(ctx, changed ? "f1Changed" : "f1");
  const members = { a: quickRun(ctx, "a"), b: quickRun(ctx, "b") };
  const loser = liveWinner.get(invocationOf(ctx)) === "a" ? "b" : "a";
  const raced = changed && n > 1 ? [members[loser]] : [members.a, members.b];
  const winner = await tick(ctx, "race", race(raced));
  if (n === 1) liveWinner.set(invocationOf(ctx), winner);
  await forceReplay(ctx, race);
  return winner;
};

// F2: two sleeps complete while a slow run is awaited alone, then race.
const subsetThenRace = (race, reversed) => async (ctx) => {
  noteAttempt(ctx, reversed ? "f2Reversed" : "f2");
  const a = tag("a")(ctx.sleep(600));
  const b = tag("b")(ctx.sleep(300));
  const slow = tag("slow")(ctx.run("slow", () => pause(1200)));
  await tick(ctx, "slow", race([slow]));
  const winner = await tick(ctx, "race", race(reversed ? [b, a] : [a, b]));
  await forceReplay(ctx, race);
  return winner;
};

// F3: a pending race kept alive by its own `then` while a new race waits.
const replacedRace = (race, keepAlive) => async (ctx) => {
  noteAttempt(ctx, keepAlive ? "f3" : "f3Dropped");
  const first = race([
    tag("s3")(ctx.sleep(3000)), tag("s4")(ctx.sleep(4000))]);
  if (keepAlive) first.then(noop, noop);
  return tick(ctx, "second", race([tag("s1")(ctx.sleep(1000))]));
};

// F4: a 2 s sliced turn with a sleep pending; the control subscribes it.
const slicedWithPending = (race, subscribed) => async (ctx) => {
  const n = noteAttempt(ctx, subscribed ? "f4Subscribed" : "f4");
  const sleep = tag("s")(ctx.sleep(300));
  if (subscribed) sleep.then(noop, noop);
  console.log("TURN start", invocationOf(ctx), n);
  await slicedTurn(20);
  console.log("TURN end", invocationOf(ctx), n);
  return tick(ctx, "after", subscribed ? sleep : race([sleep]));
};

// F9: ten runs with random delays, one race per tick.
const randomRun = (ctx, name) => tag(name)(ctx.run(name, async () => {
  await pause(Math.floor(Math.random() * 200));
  return name;
}));
const tenRuns = (race) => async (ctx) => {
  noteAttempt(ctx, "f9");
  const names = Array.from({ length: 10 }, (_, i) => `r${i}`);
  let pending = names.map((name) => ({ name, p: randomRun(ctx, name) }));
  const winners = [];
  while (pending.length > 0) {
    const label = `tick${winners.length}`;
    const won = await tick(ctx, label, race(pending.map(({ p }) => p)));
    winners.push(won);
    pending = pending.filter(({ name }) => name !== won);
  }
  console.log("ORDER", invocationOf(ctx), winners.join(","));
  await forceReplay(ctx, race);
  return winners;
};

// F10: four runs made executable by one race; each records its start.
const startOrder = (race) => async (ctx) => {
  noteAttempt(ctx, "f10");
  const startRun = (name) => tag(name)(ctx.run(name, async () => {
    effect(ctx, `start:${name}`);
    await pause(50);
    return name;
  }));
  let pending = ["r1", "r2", "r3", "r4"].map((n) => [n, startRun(n)]);
  while (pending.length > 0) {
    const won = await tick(ctx, "tick", race(pending.map(([, p]) => p)));
    pending = pending.filter(([name]) => name !== won);
  }
  return "done";
};

/** Builds the rev6-order services from the loaded SDK. */
export const orderServices = (sdk) => {
  const { race } = sdk.RestatePromise;
  const handlers = {
    f1: adjacent(race, false), f1Changed: adjacent(race, true),
    f2: subsetThenRace(race, false), f2Reversed: subsetThenRace(race, true),
    f3: replacedRace(race, true), f3Dropped: replacedRace(race, false),
    f4: slicedWithPending(race, false),
    f4Subscribed: slicedWithPending(race, true),
    f9: tenRuns(race), f10: startOrder(race)
  };
  return [
    sdk.service({ name: "Order", handlers, options: replayOptions }),
    sdk.service({ name: "OrderLive", handlers, options: retention })
  ];
};
