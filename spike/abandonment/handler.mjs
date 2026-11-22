// Spike for #31: what an abandoned SDK operation does to the attempt, with no cancellation.
import * as restate from "@restatedev/restate-sdk";

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
restate.serve({ services: [handler], port: 19892 });
