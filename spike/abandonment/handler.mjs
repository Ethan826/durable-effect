// Spike for #31: what an abandoned SDK operation does to the attempt, with no cancellation.
import * as restate from "@restatedev/restate-sdk";
import { gapServices } from "./gaps.mjs";

let attempts = {};
const note = (name) => { attempts[name] = (attempts[name] ?? 0) + 1; console.log("ATTEMPT", name, attempts[name]); };

const handler = restate.service({
  name: "Abandon",
  handlers: {
    // An operation awaited, then abandoned while pending, and a second one awaited.
    subscribedLonger: async (ctx) => {
      note("subscribedLonger");
      ctx.sleep(3000).then(() => console.log("old completed"), (e) => console.log("old rejected", e.constructor.name));
      await ctx.sleep(1000);
      return "done";
    },
    // The abandoned operation completes first, while the second is still pending.
    subscribedShorter: async (ctx) => {
      note("subscribedShorter");
      ctx.sleep(300).then(() => console.log("old completed"), (e) => console.log("old rejected", e.constructor.name));
      await ctx.sleep(1500);
      return "done";
    },
    // Control: the first operation is never subscribed.
    unsubscribed: async (ctx) => {
      note("unsubscribed");
      ctx.sleep(3000);
      await ctx.sleep(1000);
      return "done";
    },
    // The handler returns while a subscribed operation is still pending, as a detached fiber's
    // wait would be at the end of an attempt.
    returnsWithPending: async (ctx) => {
      note("returnsWithPending");
      ctx.sleep(3000).then(() => console.log("pending completed"), (e) => console.log("pending rejected", e.constructor.name));
      await ctx.run("last step", () => 1);
      return "done";
    },
    // The handler returns at once while a subscribed operation is still pending.
    returnsAtOnce: async (ctx) => {
      note("returnsAtOnce");
      ctx.sleep(3000).then(() => console.log("pending completed"), (e) => console.log("pending rejected", e.constructor.name));
      return "done";
    },
    // The abandoned operation is joined into the current wait with a combinator.
    combined: async (ctx) => {
      note("combined");
      const old = ctx.sleep(3000);
      old.then(() => console.log("old completed"), (e) => console.log("old rejected", e.constructor.name));
      await restate.RestatePromise.race([ctx.sleep(1000), old]);
      return "done";
    }
  }
});

// F1 on #46: restate-sdk-gen's per-tick pattern. Each wait is one fresh RestatePromise.race over
// the pending operations; no operation gets its own .then, .catch or single await, so a dropped
// operation is simply absent from the next race.
const { race } = restate.RestatePromise;
const tag = (label) => (promise) => promise.map(() => label);
const noteIn = (ctx, name) => note(`${ctx.request().target.service}/${name}`);
const raceHandlers = {
  // Race 3 s against 1 s, drop the 3 s sleep, then wait on a ctx.run.
  raceDropLoser: async (ctx) => {
    noteIn(ctx, "raceDropLoser");
    const first = await race([tag("slow")(ctx.sleep(3000)), tag("fast")(ctx.sleep(1000))]);
    console.log("TICK raceDropLoser first", first);
    const step = await race([ctx.run("step", () => 42)]);
    console.log("TICK raceDropLoser step", step);
    return { first, step };
  },
  // Race 3 s against 1 s, then race the still-pending 3 s against a ctx.run, then the 3 s alone.
  raceKeepLoser: async (ctx) => {
    noteIn(ctx, "raceKeepLoser");
    const slow = tag("slow")(ctx.sleep(3000));
    const first = await race([slow, tag("fast")(ctx.sleep(1000))]);
    console.log("TICK raceKeepLoser first", first);
    const second = await race([slow, ctx.run("step", () => 7).map((v) => `run:${v}`)]);
    console.log("TICK raceKeepLoser second", second);
    const third = await race([slow]);
    console.log("TICK raceKeepLoser third", third);
    return { first, second, third };
  },
  // Control: #31's failing pattern (subscribedLonger) in the same server session.
  subscribeControl: async (ctx) => {
    noteIn(ctx, "subscribeControl");
    ctx.sleep(3000).then(() => console.log("TICK subscribeControl old completed"), (e) => console.log("TICK subscribeControl old rejected", e.constructor.name));
    await ctx.sleep(1000);
    return "done";
  }
};
const retention = { journalRetention: 3600_000 };
// Live: default inactivity timeout, so each invocation runs in one stream unless an attempt fails.
const raceLive = restate.service({ name: "Race", handlers: raceHandlers, options: retention });
// Replay: a 200 ms inactivity timeout makes the server ask the SDK to suspend during each sleep,
// so every later step runs on a replay of the journal.
const replayOptions = { ...retention, inactivityTimeout: 200 };
const raceReplay = restate.service({ name: "RaceReplay", handlers: raceHandlers, options: replayOptions });

// F3 on #46: what the SDK journals for a child call when the parent is cancelled.
const child = restate.service({
  name: "Child",
  handlers: {
    slow: async (ctx) => {
      noteIn(ctx, "slow");
      try {
        await ctx.sleep(20000);
      } catch (e) {
        console.log("TICK Child/slow caught", e.constructor.name);
        throw e;
      }
      return "child done";
    }
  },
  options: retention
});
const logged = (ctx, name, body) => body().catch((e) => {
  console.log(`TICK ${ctx.request().target.service}/${name} caught`, e.constructor.name);
  throw e;
});
const parentHandlers = {
  // The parent waits on the child call itself.
  cancelSubscribedCall: async (ctx) => {
    noteIn(ctx, "cancelSubscribedCall");
    return logged(ctx, "cancelSubscribedCall", () => race([ctx.serviceClient(child).slow()]));
  },
  // The parent races the call against 1 s, drops the call, then waits on a long sleep.
  cancelReleasedCall: async (ctx) => {
    noteIn(ctx, "cancelReleasedCall");
    return logged(ctx, "cancelReleasedCall", async () => {
      const call = tag("call")(ctx.serviceClient(child).slow());
      const first = await race([call, tag("sleep")(ctx.sleep(1000))]);
      console.log("TICK cancelReleasedCall first", first);
      return race([tag("long")(ctx.sleep(60000))]);
    });
  }
};
const parentLive = restate.service({ name: "Parent", handlers: parentHandlers, options: retention });
const parentReplay = restate.service({ name: "ParentReplay", handlers: parentHandlers, options: replayOptions });

restate.serve({ services: [handler, raceLive, raceReplay, child, parentLive, parentReplay, ...gapServices], port: 19892 });
