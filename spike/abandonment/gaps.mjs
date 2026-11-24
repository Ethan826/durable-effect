// Gaps left by the F1 spike on #46: dropped calls and awakeables, a dropped operation completing
// while the handler waits on another, cancellation with a dropped operation pending, and several
// durable operations awaited together. Every wait is one fresh RestatePromise.race (or all) over
// the operations still wanted; no operation gets its own .then, .catch or bare await.
import * as restate from "@restatedev/restate-sdk";

const { race, all } = restate.RestatePromise;
const attempts = {};
const where = (ctx, name) => `${ctx.request().target.service}/${name}`;
const note = (ctx, name) => {
  const key = where(ctx, name);
  attempts[key] = (attempts[key] ?? 0) + 1;
  console.log("ATTEMPT", key, attempts[key]);
};
const tag = (label) => (promise) => promise.map((value) => (value === undefined ? label : `${label}:${value}`));

// One tick: wait on one combinator, log what it returned or the error that reached handler code.
const tick = async (ctx, name, label, combinator) => {
  try {
    const value = await combinator;
    console.log("TICK", where(ctx, name), label, JSON.stringify(value));
    return value;
  } catch (e) {
    console.log("TICK", where(ctx, name), label, "caught", e.constructor.name, e.message);
    throw e;
  }
};

// The child sleeps durably for 3 s and returns a value.
const gapChild = restate.service({
  name: "GapChild",
  handlers: {
    slow3: async (ctx) => {
      note(ctx, "slow3");
      await ctx.sleep(3000);
      console.log("TICK", where(ctx, "slow3"), "done");
      return "child done";
    }
  },
  options: { journalRetention: 3600_000 }
});
const callChild = (ctx) => tag("call")(ctx.serviceClient(gapChild).slow3());
const step = (ctx, name, value) => tag("run")(ctx.run(name, () => value));
// A ctx.run that takes a little wall time, so two runs are in flight together.
const delayed = (ctx, name, ms) => tag("run")(ctx.run(name, () => new Promise((ok) => setTimeout(() => ok(name), ms))));

const handlers = {
  // 1. Race a call to a 3 s child against 1 s, drop the call, race a ctx.run, return.
  dropCall: async (ctx) => {
    note(ctx, "dropCall");
    const first = await tick(ctx, "dropCall", "race1", race([callChild(ctx), tag("sleep1s")(ctx.sleep(1000))]));
    const second = await tick(ctx, "dropCall", "race2", race([step(ctx, "step", 1)]));
    return { first, second };
  },
  // 2. Race an awakeable nobody resolves against 1 s, drop it, race a ctx.run, return.
  dropAwakeable: async (ctx) => {
    note(ctx, "dropAwakeable");
    const awakeable = ctx.awakeable();
    console.log("AWAKEABLE", where(ctx, "dropAwakeable"), awakeable.id);
    const first = await tick(ctx, "dropAwakeable", "race1", race([tag("awk")(awakeable.promise), tag("sleep1s")(ctx.sleep(1000))]));
    const second = await tick(ctx, "dropAwakeable", "race2", race([step(ctx, "step", 2)]));
    return { first, second };
  },
  // 2b. As 2, but the dropped awakeable is resolved from outside during a 5 s race.
  dropAwakeableResolvedLater: async (ctx) => {
    note(ctx, "dropAwakeableResolvedLater");
    const awakeable = ctx.awakeable();
    console.log("AWAKEABLE", where(ctx, "dropAwakeableResolvedLater"), awakeable.id);
    const first = await tick(ctx, "dropAwakeableResolvedLater", "race1", race([tag("awk")(awakeable.promise), tag("sleep1s")(ctx.sleep(1000))]));
    const second = await tick(ctx, "dropAwakeableResolvedLater", "race2", race([tag("sleep5s")(ctx.sleep(5000))]));
    const third = await tick(ctx, "dropAwakeableResolvedLater", "race3", race([step(ctx, "step", 3)]));
    return { first, second, third };
  },
  // 3. Race 2 s against 1 s, drop the 2 s sleep, race 5 s alone: the dropped sleep completes meanwhile.
  dropCompletesMeanwhile: async (ctx) => {
    note(ctx, "dropCompletesMeanwhile");
    const first = await tick(ctx, "dropCompletesMeanwhile", "race1", race([tag("sleep2s")(ctx.sleep(2000)), tag("sleep1s")(ctx.sleep(1000))]));
    const second = await tick(ctx, "dropCompletesMeanwhile", "race2", race([tag("sleep5s")(ctx.sleep(5000))]));
    return { first, second };
  },
  // 3b. Race a 3 s child call against 1 s, drop the call, race 5 s alone: the call completes meanwhile.
  dropCallCompletesMeanwhile: async (ctx) => {
    note(ctx, "dropCallCompletesMeanwhile");
    const first = await tick(ctx, "dropCallCompletesMeanwhile", "race1", race([callChild(ctx), tag("sleep1s")(ctx.sleep(1000))]));
    const second = await tick(ctx, "dropCallCompletesMeanwhile", "race2", race([tag("sleep5s")(ctx.sleep(5000))]));
    return { first, second };
  },
  // 4. Race 30 s against 1 s, drop the 30 s sleep, race 60 s; run.sh cancels during the 60 s race.
  cancelWithDropped: async (ctx) => {
    note(ctx, "cancelWithDropped");
    const first = await tick(ctx, "cancelWithDropped", "race1", race([tag("sleep30s")(ctx.sleep(30000)), tag("sleep1s")(ctx.sleep(1000))]));
    const second = await tick(ctx, "cancelWithDropped", "race2", race([tag("sleep60s")(ctx.sleep(60000))]));
    return { first, second };
  },
  // 5. Two runs and a sleep through one all, then two runs raced, the loser kept for the next tick.
  allOfTwo: async (ctx) => {
    note(ctx, "allOfTwo");
    const both = await tick(ctx, "allOfTwo", "all", all([delayed(ctx, "a", 150), delayed(ctx, "b", 20), tag("sleep1s")(ctx.sleep(1000))]));
    const slow = delayed(ctx, "c", 150);
    const first = await tick(ctx, "allOfTwo", "race1", race([slow, delayed(ctx, "d", 20)]));
    const second = await tick(ctx, "allOfTwo", "race2", race([slow]));
    return { both, first, second };
  }
};

const retention = { journalRetention: 3600_000 };
// Live: default inactivity timeout. Replay: 200 ms, so the server suspends the handler in each wait.
const gapLive = restate.service({ name: "Gap", handlers, options: retention });
const gapReplay = restate.service({ name: "GapReplay", handlers, options: { ...retention, inactivityTimeout: 200 } });

export const gapServices = [gapChild, gapLive, gapReplay];
