import * as restate from "/Users/ethan/Desktop/durable-effect/spike/node_modules/@restatedev/restate-sdk/dist/index.js";

const handler = restate.service({
  name: "DurableReview",
  handlers: {
    replay: async ctx => {
      let synchronous = true;
      const op = ctx.run("once", () => {
        console.log("ACTION", synchronous);
        return 37;
      });
      const result = op.then(value => ({ value, synchronous }));
      synchronous = false;
      const recorded = await result;
      await ctx.sleep(25);
      return recorded;
    },
    wait: async ctx => {
      try {
        await ctx.sleep(15000);
        return { cancelled: false };
      } catch (error) {
        return { cancelled: error.constructor.name, a: await ctx.run("a", () => 11), b: await ctx.run("b", () => 12) };
      }
    },
    wrap: async ctx => {
      await ctx.sleep(2 ** 64 + 4096);
      return "completed";
    },
    sample: async ctx => {
      await ctx.sleep(10);
      try {
        await ctx.run("delayed sample", () => new Promise(resolve => setTimeout(() => resolve(19), 2500)));
        return { cancelled: false };
      } catch (error) {
        return { cancelled: error.constructor.name, retrySample: await ctx.run("replacement sample", () => 23) };
      }
    },
    two: async (ctx, subscribeOld) => {
      let listening = true;
      const old = ctx.sleep(15000);
      if (subscribeOld) old.then(
        () => console.log("old completed", listening),
        error => console.log("old rejected", error.constructor.name, listening)
      );
      listening = false;
      try {
        await ctx.sleep(3000);
        return { cancelled: false };
      } catch (error) {
        return { cancelled: error.constructor.name };
      }
    }
  }
});
restate.serve({ services: [handler], port: 19882 });
