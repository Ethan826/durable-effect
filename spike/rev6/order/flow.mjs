// rev6-order fixtures F5 to F8 (register on #48, A19, A20, A21, A22),
// with the child services they call.
import {
  noteAttempt, tag, tick, pause, effect, slicedTurn, invocationOf,
  retention, replayOptions
} from "./lib.mjs";

const noop = () => undefined;

const childServices = (sdk) => {
  const child = sdk.service({
    name: "OrdChild",
    handlers: {
      sleepFor: async (ctx, ms) => {
        await ctx.sleep(ms);
        return ms;
      },
      failAfter: async (ctx, ms) => {
        await ctx.sleep(ms);
        throw new sdk.TerminalError("child failed", { errorCode: 499 });
      },
      stamp: async (_ctx, parent) => {
        console.log("CHILDSTART", parent, Date.now());
        return "stamped";
      }
    },
    options: retention
  });
  const resolver = sdk.service({
    name: "OrdResolver",
    handlers: {
      resolveLater: async (ctx, { id, ms }) => {
        await ctx.sleep(ms);
        ctx.resolveAwakeable(id, "resolved");
        return "sent";
      }
    },
    options: retention
  });
  return { child, resolver };
};

// F5: calls, runs, sleeps and an awakeable in one race, over many ticks.
const slowRun = (ctx, name, ms) =>
  ctx.run(name, () => pause(ms).then(() => name));
const manyOps = (ctx, { child, resolver }) => {
  const calls = ctx.serviceClient(child);
  const awakeable = ctx.awakeable();
  const resolve = ctx.serviceClient(resolver)
    .resolveLater({ id: awakeable.id, ms: 700 });
  return [
    ["call1", calls.sleepFor(900)], ["call2", calls.sleepFor(1700)],
    ["run1", slowRun(ctx, "run1", 100)], ["run2", slowRun(ctx, "run2", 300)],
    ["sleep1", ctx.sleep(500)], ["sleep2", ctx.sleep(1300)],
    ["awk", awakeable.promise], ["resolver", resolve]
  ].map(([name, p]) => ({ name, p: tag(name)(p) }));
};
const manyInFlight = (race, deps) => async (ctx) => {
  noteAttempt(ctx, "f5");
  let pending = manyOps(ctx, deps);
  const winners = [];
  while (pending.length > 0) {
    const won = await tick(ctx, `tick${winners.length}`,
      race(pending.map(({ p }) => p)));
    winners.push(won);
    pending = pending.filter(({ name }) => !won.startsWith(name));
  }
  return winners;
};

// #31's failing pattern, the control for F5 and F7.
const subscribedLonger = async (ctx) => {
  noteAttempt(ctx, "subscribedLonger");
  ctx.sleep(3000).then(noop, noop);
  await ctx.sleep(1000);
  return "done";
};
const returnsWithPending = async (ctx) => {
  noteAttempt(ctx, "returnsWithPending");
  ctx.sleep(3000).then(noop, noop);
  await ctx.run("last step", () => 1);
  return "done";
};

// F6: a dropped operation fails while a later race waits.
const failingRun = (ctx, sdk, terminal, n) => ctx.run("failing", async () => {
  effect(ctx, `f6run:${terminal ? "terminal" : "retryable"}`);
  await pause(300);
  if (terminal) throw new sdk.TerminalError("run failed");
  if (n === 1) throw new Error("retryable run failure");
  return "ok";
});
const droppedOp = (ctx, sdk, deps, kind, n) => {
  const ops = {
    call: () => ctx.serviceClient(deps.child).failAfter(300),
    run: () => failingRun(ctx, sdk, true, n),
    retry: () => failingRun(ctx, sdk, false, n)
  };
  return ops[kind]();
};
const droppedFails = (race, sdk, deps, kind) => async (ctx) => {
  const n = noteAttempt(ctx, `f6${kind}`);
  const awakeable = kind === "awk" ? ctx.awakeable() : undefined;
  const op = awakeable?.promise ?? droppedOp(ctx, sdk, deps, kind, n);
  await tick(ctx, "first",
    race([tag("op")(op), tag("short")(ctx.sleep(100))]));
  if (awakeable) ctx.rejectAwakeable(awakeable.id, "rejected");
  await tick(ctx, "second", race([tag("long")(ctx.sleep(1000))]));
  return "done";
};

// F7: the root returns with a race pending, a run executing, a call out.
const returnsMidRace = (race, deps) => async (ctx) => {
  noteAttempt(ctx, "f7");
  const call = tag("call")(ctx.serviceClient(deps.child).sleepFor(1500));
  const run = tag("run")(ctx.run("slow", async () => {
    effect(ctx, "f7run:start");
    await pause(1500);
    effect(ctx, "f7run:end");
    return 1;
  }));
  const pending = race([call, run, tag("s")(ctx.sleep(3000))]);
  pending.then((v) => console.log("LATE", invocationOf(ctx), v), noop);
  await pause(300);
  console.log("RETURN", invocationOf(ctx));
  return "done";
};

// F8: when a call issued before a 2 s turn reaches the server.
const callAfterTurn = (race, deps, late) => async (ctx) => {
  noteAttempt(ctx, late ? "f8" : "f8AtOnce");
  console.log("ISSUE", invocationOf(ctx), Date.now());
  const call = ctx.serviceClient(deps.child).stamp(invocationOf(ctx));
  if (late) await slicedTurn(20);
  if (late) console.log("TURNEND", invocationOf(ctx), Date.now());
  return tick(ctx, "call", race([tag("call")(call)]));
};

/** Builds the F5 to F8 services, and their children, from the SDK. */
export const flowServices = (sdk) => {
  const { race } = sdk.RestatePromise;
  const deps = childServices(sdk);
  const handlers = {
    f5: manyInFlight(race, deps), subscribedLonger, returnsWithPending,
    f6call: droppedFails(race, sdk, deps, "call"),
    f6run: droppedFails(race, sdk, deps, "run"),
    f6awk: droppedFails(race, sdk, deps, "awk"),
    f6retry: droppedFails(race, sdk, deps, "retry"),
    f7: returnsMidRace(race, deps),
    f8: callAfterTurn(race, deps, true),
    f8AtOnce: callAfterTurn(race, deps, false)
  };
  return [
    deps.child, deps.resolver,
    sdk.service({ name: "Flow", handlers, options: replayOptions }),
    sdk.service({ name: "FlowLive", handlers, options: retention })
  ];
};
