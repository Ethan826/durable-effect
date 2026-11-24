// A5, scripted against the SDK's own wasm VM (WasmVM in @restatedev/restate-sdk's bundled
// sdk-shared-core bindings). The test feeds encoded protocol frames and drives one race the way
// the SDK's PromisesExecutor does (promises.ts doProgressInner: take every member's notification,
// then do_progress on the race, wait for input on WaitExternalProgress, reject on
// CancelSignalReceived). It prints one RESULT line per scenario and per protocol version.
//
// A5: if a tracked call's invocation id has not arrived when the cancel is popped, the VM returns
// without delivering the cancel; a race member ready meanwhile wins and the cancel goes to the
// next await. Control: with the id already delivered, the cancel comes first.
import { messages, splitFrames, fields, text, TYPE } from "./proto.mjs";

const sdkDir = process.env.SDK_DIR;
const bindings = await import(`${sdkDir}/dist/endpoint/handlers/vm/sdk_shared_core_wasm_bindings.js`);
const { WasmVM, WasmHeader, LogLevel, WasmJournalMismatchBehavior } = bindings;

const CHILD_ID = "inv_1childAAAAAAAAAAAAAAAAAAAAAAAAAAA";

const newVm = (version) => new WasmVM(
  [new WasmHeader("content-type", `application/vnd.restate.invocation.v${version}`)],
  LogLevel.WARN, 0, false, false, WasmJournalMismatchBehavior.Retry, false
);

// Starts an invocation with one Input command, opens the stream (input not closed) and issues a
// call and a sleep, as `race([ctx.serviceClient(child).slow(), ctx.sleep(1000)])` would.
const begin = (version) => {
  const vm = newVm(version);
  vm.notify_input(messages.start(1));
  vm.notify_input(messages.input("null"));
  if (!vm.is_ready_to_execute()) throw new Error("VM not ready after start and input");
  vm.sys_input();
  const call = vm.sys_call("Child", "slow", new Uint8Array(), null, [], null, null, null, null);
  const sleep = vm.sys_sleep(BigInt(Date.now() + 1000), null);
  return { vm, call, sleep, out: [] };
};

const drain = (session) => {
  for (;;) {
    const chunk = session.vm.take_output();
    if (!(chunk instanceof Uint8Array) || chunk.length === 0) return;
    session.out.push(chunk);
  }
};

// Completion ids are read back from the commands the VM wrote, not assumed.
const completionIds = (session) => {
  drain(session);
  const frames = splitFrames(session.out);
  const call = fields(frames.find((f) => f.type === TYPE.call).body);
  const sleep = fields(frames.find((f) => f.type === TYPE.sleep).body);
  return { callId: Number(call[10][0]), callResult: Number(call[11][0]), sleep: Number(sleep[11][0]) };
};

// One await on a race, as PromisesExecutor.doProgressInner runs it. `pending` is the input still
// to arrive, delivered one frame per WaitExternalProgress.
const awaitRace = (session, members, pending, trace) => {
  const { vm } = session;
  for (let step = 0; step < 20; step++) {
    const ready = members.find((m) => vm.take_notification(m.handle) !== "NotReady");
    if (ready) return { outcome: `member:${ready.label}` };
    const result = vm.do_progress({ FirstCompleted: members.map((m) => ({ Single: m.handle })) });
    trace.push(typeof result === "string" ? result : JSON.stringify(result));
    if (result === "CancelSignalReceived") return { outcome: "cancelled" };
    if (result === "WaitExternalProgress") {
      const next = pending.shift();
      if (!next) return { outcome: "waiting" };
      trace.push(`deliver ${next.label}`);
      vm.notify_input(next.bytes);
    } else if (result !== "AnyCompleted") return { outcome: `other:${trace.at(-1)}` };
  }
  return { outcome: "no-progress" };
};

const sendSignals = (session) => {
  drain(session);
  return splitFrames(session.out)
    .filter((f) => f.type === TYPE.sendSignal)
    .map((f) => text(fields(f.body)[1]?.[0]));
};

const commandNames = (session) => {
  drain(session);
  return splitFrames(session.out).map((f) => f.name);
};

// Runs one scenario: `queued` frames arrive before the first await, `later` frames arrive one per
// WaitExternalProgress. The second await is a race over a fresh sleep, as the next turn would be.
const scenario = (version, queuedOf, laterOf) => {
  const session = begin(version);
  const ids = completionIds(session);
  const frames = {
    id: { label: "CallInvocationId", bytes: messages.callId(ids.callId, CHILD_ID) },
    cancel: { label: "cancel signal", bytes: messages.cancel() },
    sleepDone: { label: "sleep completion", bytes: messages.sleepDone(ids.sleep) }
  };
  queuedOf.forEach((name) => session.vm.notify_input(frames[name].bytes));
  const later = laterOf.map((name) => frames[name]);
  const trace1 = [];
  const first = awaitRace(session, [{ label: "call", handle: session.call.call_completion_id }, { label: "sleep", handle: session.sleep }], later, trace1);
  const signalsAfterFirst = sendSignals(session);
  const nextSleep = session.vm.sys_sleep(BigInt(Date.now() + 60000), null);
  const trace2 = [];
  const second = awaitRace(session, [{ label: "sleep2", handle: nextSleep }], [], trace2);
  return { ids, first: first.outcome, trace1, signalsAfterFirst, second: second.outcome, trace2, signalsAfterSecond: sendSignals(session), commands: commandNames(session) };
};

// A5's pass criterion: the race member wins the first await with no SendSignal written, and the
// second await reports the cancel with exactly one SendSignal to the call.
const a5Holds = (r) => r.first === "member:sleep" && r.signalsAfterFirst.length === 0
  && r.second === "cancelled" && r.signalsAfterSecond.length === 1 && r.signalsAfterSecond[0] === CHILD_ID;

const versions = (process.env.A5_VERSIONS ?? "5,6,7,8").split(",").map(Number);
let failures = 0;
for (const version of versions) {
  // Main: the cancel and then the sleep's completion are queued; the call's id arrives later.
  const main = scenario(version, ["cancel", "sleepDone"], ["id"]);
  // Control: the id is already delivered when the cancel and the sleep's completion arrive.
  const control = scenario(version, ["id", "cancel", "sleepDone"], []);
  console.log(`A5 v${version} main    ${JSON.stringify(main)}`);
  console.log(`A5 v${version} control ${JSON.stringify(control)}`);
  const mainOk = a5Holds(main);
  const controlFails = !a5Holds(control);
  failures += mainOk && controlFails ? 0 : 1;
  console.log(`RESULT A5 v${version} ${mainOk ? "PASS" : "FAIL"}: main first await ${main.first}, SendSignal after first ${main.signalsAfterFirst.length}, second await ${main.second}, SendSignal after second ${JSON.stringify(main.signalsAfterSecond)}`);
  console.log(`RESULT A5-control v${version} ${controlFails ? "FAILS AS REQUIRED" : "DID NOT FAIL (finding)"}: control first await ${control.first}, SendSignal after first ${JSON.stringify(control.signalsAfterFirst)}`);
}
process.exitCode = failures === 0 ? 0 : 1;
