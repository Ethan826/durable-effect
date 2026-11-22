import assert from "node:assert/strict";
import { createRequire } from "node:module";
import { setImmediate as next } from "node:timers/promises";

const root = "/Users/ethan/Desktop/durable-effect/spike/node_modules";
const require = createRequire(import.meta.url);
const { Effect, Fiber, Ref, Scheduler, Clock } = await import(root + "/effect/dist/index.js");
const sdk = root + "/@restatedev/restate-sdk/dist";
const { PromisesExecutor, SingleRestatePromise } = await import(sdk + "/promises.js");
const { ContextImpl } = await import(sdk + "/context_impl.js");
const { millisOrDurationToMillis } = await import(root + "/@restatedev/restate-sdk-core/dist/duration.js");
console.log("versions", ...["effect", "@restatedev/restate-sdk"].map(p => require(root + "/" + p + "/package.json").version));

let pending = [];
const dispatcher = new Scheduler.MixedScheduler("async", fn => {
  pending.push(fn);
  return () => {};
}).makeDispatcher();
const priority = [];
dispatcher.scheduleTask(() => priority.push("queued p=0"), 0);
dispatcher.scheduleTask(() => priority.push("yield p=-1"), -1);
dispatcher.scheduleTask(() => priority.push("second queued p=0"), 0);
dispatcher.flush();
assert.deepEqual(priority, ["yield p=-1", "queued p=0", "second queued p=0"]);
console.log("priority", priority);

const events = [];
let parent;
let turn = true;
const sc = {
  ...new Scheduler.MixedScheduler(),
  makeDispatcher: () => dispatcher,
  shouldYield: f => {
    if (!turn) events.push("guard outside");
    return f.currentOpCount >= f.cache.maxOpsBeforeYield;
  }
};
const record = value => Effect.sync(() => events.push(value));
const forkProbe = Effect.gen(function* () {
  parent = Fiber.getCurrent();
  yield* Effect.forkChild(record("queued child"));
  yield* Effect.forkChild(Effect.sync(() => events.push(
    Fiber.getCurrent() === parent ? "wrong child identity" : "inline child identity"
  )), { startImmediately: true });
  yield* Effect.sync(() => events.push(
    Fiber.getCurrent() === parent ? "parent restored" : "wrong parent identity"
  ));
  yield* Effect.yieldNow;
  yield* record("parent after yield");
});
Effect.runFork(forkProbe, { scheduler: sc });
dispatcher.flush();
assert.deepEqual(events, ["inline child identity", "parent restored", "queued child", "parent after yield"]);
console.log("E3/E8", events.splice(0));

const interruptProbe = Effect.gen(function* () {
  const ref = yield* Ref.make(0);
  const child = yield* Effect.forkChild(Effect.ensuring(
    Effect.never, Effect.yieldNow.pipe(Effect.andThen(Ref.set(ref, 1)))
  ), { startImmediately: true });
  yield* Fiber.interrupt(child);
  events.push(["after interrupt:", yield* Ref.get(ref)]);
});
Effect.runFork(interruptProbe, { scheduler: sc });
dispatcher.flush();
assert.deepEqual(events, [["after interrupt:", 1]]);
console.log("interrupt", events.splice(0));

let notify;
Effect.runFork(Effect.callback(resume => { notify = resume; }), { scheduler: sc });
turn = false;
notify(record("callback body"));
turn = true;
assert.equal(events[0], "guard outside");
assert.ok(events.indexOf("callback body") > 0);
console.log("E1/E4 callback", events.splice(0));

const controller = new AbortController();
Effect.runFork(
  Effect.ensuring(Effect.never, record("abort finalizer")),
  { scheduler: sc, signal: controller.signal }
);
turn = false;
controller.abort();
turn = true;
assert.equal(events[0], "guard outside");
assert.ok(events.indexOf("abort finalizer") > 0);
console.log("E1/E4 abort", events.splice(0));

const cacheProbe = Effect.gen(function* () {
  const cached = yield* Effect.cached(record("cache body"));
  yield* cached;
});
Effect.runFork(cacheProbe, { scheduler: sc });
dispatcher.flush();
turn = false;
await next();
turn = true;
assert.deepEqual(events, ["cache body"]);
console.log("E2 cache case", events.splice(0));

const outputPump = { awaitNextProgress: () => Promise.resolve() };
const faults = [];
let sentCancel = false;
const order = [];
const core = {
  take_notification: handle => handle === 3 ? "journaled value" : "NotReady",
  do_progress: ({ Single }) => {
    order.push(["progress", Single]);
    if (!sentCancel) {
      sentCancel = true;
      return "CancelSignalReceived";
    }
    return "WaitExternalProgress";
  }
};
const executor = new PromisesExecutor(core, outputPump, {}, {}, { awaitNext: () => new Promise(() => {}) },
  error => faults.push(error));
const ctx = { coreVm: core, promisesExecutor: executor };
const resolveNotification = (value, { resolve }) => resolve(value);
const replay = new SingleRestatePromise(ctx, 3, resolveNotification);
const replayed = replay.then(value => order.push(["replayed", value]));
order.push("sync after attaching");
await replayed;
assert.deepEqual(order.splice(0), ["sync after attaching", ["replayed", "journaled value"]]);
console.log("E6 SDK JS layer", "sync after attaching -> replayed journaled value");

const abandoned = new SingleRestatePromise(ctx, 1, resolveNotification);
const current = new SingleRestatePromise(ctx, 2, resolveNotification);
let listening = true;
const seen = [];
const before = abandoned.then(() => {}, error => {
  seen.push([1, error.constructor.name, listening]);
});
listening = false;
current.then(() => {}, error => seen.push([2, error.constructor.name, true]));
await before;
await next();
assert.deepEqual(seen, [[1, "CancelledError", false]]);
assert.deepEqual(faults, []);
console.log("E5b mocked VM", order, seen);

let closure;
const runOrder = [];
let complete = false;
const runCore = {
  sys_run: name => { runOrder.push(["command", name]); return { handle: 4, replayed: false }; },
  last_command_index: () => 0,
  take_notification: () => complete ? { Success: new Uint8Array() } : "NotReady",
  do_progress: () => ({ ExecuteRun: 4 }),
  propose_run_completion_success: () => { complete = true; }
};
const runContext = {
  coreVm: runCore, defaultSerde: { serialize: () => new Uint8Array() },
  journalValueCodec: { encode: value => value },
  runInterceptor: async (_name, action) => await action(), outputPump,
  runClosuresTracker: {
    registerRunClosure: (_handle, action) => { closure = action; },
    executeRun: () => { runOrder.push("progress executes closure"); void closure(); }
  },
  abortAttempt: error => faults.push(error)
};
runContext.promisesExecutor = new PromisesExecutor(runCore, outputPump, runContext.runClosuresTracker,
  {}, {}, error => faults.push(error));
const operation = ContextImpl.prototype.run.call(runContext, "review", () => runOrder.push("action"));
runOrder.push("returned from run");
operation.then(() => {}, () => {});
await next();
await next();
await next();
assert.deepEqual(runOrder, [["command", "review"], "returned from run", "progress executes closure", "action"]);
console.log("E9 mocked VM", runOrder);

assert.equal(millisOrDurationToMillis(1.9), 1);
console.log("E7 JS conversion", millisOrDurationToMillis(1.9));
const unsafe = 2 ** 53;
console.log("number precision", unsafe, unsafe + 1, (unsafe + 1) - unsafe);
assert.equal((unsafe + 1) - unsafe, 0);

const finalizerValues = [];
await Effect.runPromise(Effect.ensuring(
  Effect.succeed(1), Effect.sync(() => finalizerValues.push("normal"))
));
assert.deepEqual(finalizerValues, ["normal"]);
console.log("normal finalizer", finalizerValues);
const idOne = await Effect.runPromise(Effect.fiberId);
const idTwo = await Effect.runPromise(Effect.fiberId);
assert.notEqual(idOne, idTwo);
console.log("attempt root fiber ids", idOne, idTwo);
