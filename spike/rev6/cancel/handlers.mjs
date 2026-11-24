// Handlers for the rev6-cancel (F12 to F16) and rev6-replay-checks (F20) fixtures of the
// assumptions register on #48. Every wait on a durable operation is one fresh
// RestatePromise.race over the operations still wanted; no operation gets its own .then.
//
// Log lines the driver reads:
//   ATTEMPT <service>/<handler> <n> <invocation id>   n counts attempts of that invocation in
//                                                     this SDK process
//   EVENT <invocation id> <json>                      a step's outcome, with the attempt number
//   ACTION <invocation id> <name> <n>                 a ctx.run action body executed (n-th time)
import http2 from "node:http2";

const sdk = await import(`${process.env.SDK_DIR}/dist/index.js`);
const { RestatePromise, TerminalError } = sdk;
const { race } = RestatePromise;

const attempts = new Map();
const actions = new Map();
const invocation = (ctx) => ctx.request().id;
const attemptOf = (ctx) => attempts.get(invocation(ctx)) ?? 0;
const begin = (ctx, handler) => {
  const id = invocation(ctx);
  const n = (attempts.get(id) ?? 0) + 1;
  attempts.set(id, n);
  console.log("ATTEMPT", `${ctx.request().target.service}/${handler}`, n, id);
};
const event = (ctx, body) => console.log("EVENT", invocation(ctx), JSON.stringify({ attempt: attemptOf(ctx), ...body, at: Date.now() }));
const wait = (ms) => new Promise((resolve) => setTimeout(resolve, ms));
// A ctx.run action that counts its executions per invocation.
const counted = (ctx, name, body) => async () => {
  const key = `${invocation(ctx)} ${name}`;
  const n = (actions.get(key) ?? 0) + 1;
  actions.set(key, n);
  console.log("ACTION", invocation(ctx), name, n);
  return body();
};
const errorOf = (e) => ({ error: e?.constructor?.name, code: e?.code, message: e?.message });
// Awaits one combinator and records how it settled and how long it took; never throws.
const settle = async (ctx, step, combinator) => {
  event(ctx, { step: `${step}:start` });
  const started = Date.now();
  try {
    const value = await combinator;
    const outcome = { step, settled: "resolved", value, ms: Date.now() - started };
    event(ctx, outcome);
    return outcome;
  } catch (e) {
    const outcome = { step, settled: "rejected", ...errorOf(e), ms: Date.now() - started };
    event(ctx, outcome);
    return outcome;
  }
};
const rethrowIfRejected = (outcome, cause) => {
  if (outcome.settled === "rejected") throw cause();
};
const cancelled = () => new TerminalError("Cancelled", { errorCode: 409 });

// ---- children ----
const child = sdk.service({
  name: "CxChild",
  handlers: {
    fast: async (ctx, arg) => `fast:${arg}`,
    slow: async (ctx, ms) => {
      await ctx.sleep(ms);
      return `slow:${ms}`;
    }
  },
  options: { journalRetention: 3600_000 }
});
const callFast = (ctx, arg) => ctx.serviceClient(child).fast(arg);
const callSlow = (ctx, ms) => ctx.serviceClient(child).slow(ms);

// ---- F12 cancelSet: a completed, a dropped and a pending call, then a cancel ----
// With `explicit`, the handler races the third call against ctx.cancellation(), the way a
// handler under explicitCancellation: true observes a cancel; nothing else changes.
const cancelSet = (explicit) => async (ctx) => {
  begin(ctx, "cancelSet");
  await settle(ctx, "a", race([callFast(ctx, "A")]));
  await settle(ctx, "b", race([callSlow(ctx, 30000), ctx.sleep(500).map(() => "sleep500")]));
  const explicitMember = explicit
    ? [sdk.internal.asInternal(ctx).cancellation().map(() => { throw cancelled(); })]
    : [];
  const third = await settle(ctx, "c", race([callSlow(ctx, 30000), ctx.sleep(60000).map(() => "sleep60s"), ...explicitMember]));
  if (third.settled === "resolved") return "not cancelled";
  event(ctx, { step: "comp-start" });
  await settle(ctx, "comp", race([ctx.run("comp", counted(ctx, "comp", () => wait(4000).then(() => "comp")))]));
  throw cancelled();
};

// ---- F13 childrenSurvive: cancel during a race of a run, a call and a sleep ----
const survivors = (ctx) => {
  const run = ctx.run("r", counted(ctx, "r", () => wait(10000).then(() => "r-value")));
  const call = callSlow(ctx, 30000);
  const sleep = ctx.sleep(15000).map(() => "slept");
  return { run, call, sleep, combinator: race([run, call, sleep]) };
};
const childrenSurvive = async (ctx) => {
  begin(ctx, "childrenSurvive");
  const { run, call, sleep, combinator } = survivors(ctx);
  const first = await settle(ctx, "k", combinator);
  const reRun = await settle(ctx, "reRun", race([run]));
  const reCall = await settle(ctx, "reCall", race([call]));
  const reSleep = await settle(ctx, "reSleep", race([sleep]));
  return { first, reRun, reCall, reSleep };
};
// Control: await the rejected combinator again.
const deadCombinator = async (ctx) => {
  begin(ctx, "deadCombinator");
  const { combinator } = survivors(ctx);
  const first = await settle(ctx, "k", combinator);
  const again = await settle(ctx, "kAgain", combinator);
  return { first, again };
};
// Control: a single operation awaited alone, cancelled, then awaited again.
const singleCancelled = async (ctx) => {
  begin(ctx, "singleCancelled");
  const sleep = ctx.sleep(60000);
  const first = await settle(ctx, "single", sleep);
  const again = await settle(ctx, "singleAgain", sleep);
  return { first, again };
};

// ---- F14 compensate and F15 secondCancel ----
const cancelThenCompensate = async (ctx, name, compensation) => {
  begin(ctx, name);
  await settle(ctx, "x", race([callSlow(ctx, 30000), ctx.sleep(60000).map(() => "sleep60s")]));
  event(ctx, { step: "comp-start" });
  return compensation(ctx);
};
const compensate = (ctx) => cancelThenCompensate(ctx, "compensate", async () => ({
  refund: await settle(ctx, "refund", race([callFast(ctx, "refund")])),
  run: await settle(ctx, "compRun", race([ctx.run("compRun", counted(ctx, "compRun", () => "ran"))])),
  sleep: await settle(ctx, "compSleep", race([ctx.sleep(1000).map(() => "slept")]))
}));
const secondCancel = (ctx) => cancelThenCompensate(ctx, "secondCancel", async () => ({
  y: await settle(ctx, "y", race([callSlow(ctx, 10000)])),
  after: await settle(ctx, "after", race([ctx.run("after", counted(ctx, "after", () => "after"))]))
}));

// ---- F16 cancelAtAwait ----
// A busy turn: handler code runs for 8 s with no durable await. The server takes about 2.3 s to
// journal a cancel, so a cancel sent 1.5 s into the turn arrives well inside it.
const busy = async (ctx) => {
  event(ctx, { step: "busy-start" });
  await wait(8000);
  event(ctx, { step: "busy-end" });
};
const act = (ctx) => ctx.run("act", counted(ctx, "act", () => "acted"));
const cancelAtAwait = async (ctx) => {
  begin(ctx, "cancelAtAwait");
  const run = act(ctx);
  await busy(ctx);
  const raced = await settle(ctx, "raceR", race([run]));
  return { raced };
};
const rootNoAwait = async (ctx) => {
  begin(ctx, "rootNoAwait");
  act(ctx);
  await busy(ctx);
  return "done";
};
const emptyRace = async (ctx) => {
  begin(ctx, "emptyRace");
  await busy(ctx);
  const timeout = wait(1500).then(() => "timeout");
  const empty = await settle(ctx, "empty", Promise.race([race([]).map(() => "empty race"), timeout]));
  const observed = await settle(ctx, "observe", race([ctx.sleep(100).map(() => "slept")]));
  rethrowIfRejected(observed, cancelled);
  return { empty, observed };
};
// Control: race the run before the busy turn.
const raceFirst = async (ctx) => {
  begin(ctx, "raceFirst");
  const raced = await settle(ctx, "raceR", race([act(ctx)]));
  await busy(ctx);
  const after = await settle(ctx, "after", race([ctx.sleep(100).map(() => "slept")]));
  return { raced, after };
};

// ---- F20 mismatch matrix: attempt 1 writes the journal, later attempts replay a changed form ----
const replayed = (ctx) => attemptOf(ctx) >= 2;
const thenSleep = async (ctx, result) => {
  await settle(ctx, "tail", race([ctx.sleep(1000).map(() => "slept")]));
  return result;
};
const matrix = {
  callParam: async (ctx) => {
    begin(ctx, "callParam");
    const value = await settle(ctx, "call", race([callFast(ctx, replayed(ctx) ? "B" : "A")]));
    return thenSleep(ctx, value);
  },
  runName: async (ctx) => {
    begin(ctx, "runName");
    const name = replayed(ctx) ? "r2" : "r1";
    const value = await settle(ctx, "run", race([ctx.run(name, counted(ctx, name, () => 1))]));
    return thenSleep(ctx, value);
  },
  sleepDuration: async (ctx) => {
    begin(ctx, "sleepDuration");
    const value = await settle(ctx, "sleep", race([ctx.sleep(replayed(ctx) ? 900 : 600).map(() => "slept")]));
    return thenSleep(ctx, value);
  },
  swappedAwakeables: async (ctx) => {
    begin(ctx, "swappedAwakeables");
    const first = ctx.awakeable();
    const second = ctx.awakeable();
    event(ctx, { step: "awakeables", ids: [first.id, second.id] });
    const order = replayed(ctx) ? [second, first] : [first, second];
    const members = [...order.map((a) => a.promise), ctx.sleep(600).map(() => "slept")];
    return thenSleep(ctx, await settle(ctx, "race", race(members)));
  },
  raceMembers: async (ctx) => {
    begin(ctx, "raceMembers");
    const short = ctx.sleep(600).map(() => "short");
    const long = ctx.sleep(5000).map(() => "long");
    const members = replayed(ctx) ? [short] : [short, long];
    return thenSleep(ctx, await settle(ctx, "race", race(members)));
  },
  identical: async (ctx) => {
    begin(ctx, "identical");
    const call = await settle(ctx, "call", race([callFast(ctx, "A")]));
    const run = await settle(ctx, "run", race([ctx.run("count", counted(ctx, "count", () => 1))]));
    return thenSleep(ctx, { call, run });
  }
};

// ---- services ----
const retention = { journalRetention: 3600_000 };
const replay = { ...retention, inactivityTimeout: 200 };
const cancelHandlers = {
  cancelSet: cancelSet(false), childrenSurvive, deadCombinator, singleCancelled,
  compensate, secondCancel, cancelAtAwait, rootNoAwait, emptyRace, raceFirst
};
const services = [
  child,
  // Live: default inactivity timeout, so each invocation runs in one attempt unless it fails.
  sdk.service({ name: "CxLive", handlers: cancelHandlers, options: retention }),
  // Replay: a 200 ms inactivity timeout suspends the handler in every wait.
  sdk.service({ name: "CxReplay", handlers: cancelHandlers, options: replay }),
  sdk.service({ name: "CxExplicit", handlers: { cancelSet: cancelSet(true) }, options: { ...retention, explicitCancellation: true } }),
  sdk.service({ name: "CxMatrix", handlers: matrix, options: replay })
];
// The same matrix behind a journal value codec, which turns the SDK's payload checks off.
const identityCodec = { encode: (buf) => buf, decode: (buf) => Promise.resolve(buf) };
const codecServices = [sdk.service({ name: "CxCodec", handlers: matrix, options: replay })];

const main = sdk.createEndpointHandler({ services });
const codec = sdk.createEndpointHandler({ services: codecServices, journalValueCodecProvider: () => Promise.resolve(identityCodec) });
const port = Number(process.env.SDK_PORT);
http2.createServer((req, res) => (req.url.startsWith("/codec/") ? codec(req, res) : main(req, res))).listen(port, "127.0.0.1", () => {
  console.log("SDK-LISTENING", port, "pid", process.pid);
});
