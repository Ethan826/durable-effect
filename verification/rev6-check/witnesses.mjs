// witnesses.mjs: one witness per mutant for the gate integrity check. Each is a
// program in step 7 grammar and a choice path along which the mutant history
// differs, as JSON, from the base model history. `choices` is the exact
// label sequence `step` accepts under the mutant, and `baseChoices` the
// one under the base model, which may differ where the mutant changes what
// the schedule offers. Both use model.mjs default (reduced) limits.
// replayWitness(name, options) replays one: options.mutant names the
// mutant; without it the base model runs baseChoices.

import * as M from "./model.mjs";

/** Mutant name -> { program, choices, baseChoices, note }. */
export const mutantWitnesses = {
  noM1: {
    program:
      {"fibers":[{"id":"f0","daemon":false,"body":[{"s":"sleep","op":"s1",
      "ms":1},{"s":"sleep","op":"s2","ms":2},{"s":"sleep","op":"s3","ms":0},{
      "s":"race","ops":["s1","s2"]},{"s":"await","op":"s3"}]}]},
    choices: [
      "sample:0:0", "fire:2", "fire:3", "fire:4", "sample:6:0",
      "sample:10:0", "sample:12:0",
    ],
    baseChoices: [
      "sample:0:0", "fire:2", "fire:3", "fire:4", "sample:6:0",
      "sample:10:0",
    ],
    note:
      "s2's result is queued behind the race winner s1; base drops it at the " +
      "head (M1), the mutant gives it a turn and a sample",
  },
  rev5Credit: {
    program:
      {"fibers":[{"id":"f0","daemon":false,"body":[{"s":"sleep","op":"s1",
      "ms":2},{"s":"sleep","op":"s2","ms":2},{"s":"await","op":"s1"},{
      "s":"await","op":"s2"},{"s":"clock"}]}]},
    choices: [
      "sample:0:0", "fire:2", "sample:5:0", "fire:3", "sample:8:0",
    ],
    baseChoices: [
      "sample:0:0", "fire:2", "sample:5:0", "fire:3", "sample:8:0",
    ],
    note:
      "two 2 ms sleeps issued in one turn: the anchored rule " +
      "credits a+2 once " +
      "(clock 2), revision 5 credits L+2 twice (clock 4)",
  },
  deliveryAnchor: {
    program:
      {"fibers":[{"id":"f0","daemon":false,"body":[{"s":"sleep","op":"s1",
      "ms":2},{"s":"sleep","op":"s2","ms":2},{"s":"await","op":"s1"},{
      "s":"await","op":"s2"},{"s":"clock"}]}]},
    choices: [
      "sample:0:0", "fire:2", "sample:5:0", "fire:3", "sample:8:0",
    ],
    baseChoices: [
      "sample:0:0", "fire:2", "sample:5:0", "fire:3", "sample:8:0",
    ],
    note:
      "as rev5Credit: anchoring at delivery adds the second sleep's 2 ms on " +
      "top of the first's credit",
  },
  noEntryGate: {
    program:
      {"fibers":[{"id":"f0","daemon":false,"body":[{"s":"run","op":"r1",
      "behaviour":"ignoreOk"},{"s":"await","op":"r1"}]}]},
    choices: [
      "sample:0:0", "cancel", "crash", "sample:4:0", "settle:2", "ack:2",
    ],
    baseChoices: [
      "sample:0:0", "cancel", "crash", "sample:4:0", "ack:2",
    ],
    note:
      "C24's window: attempt 0 crashes after consuming a cancel but before " +
      "its turn's sample settles; on replay r1's wrapper is called while the " +
      "cancel is consumed and not yet acted on. Base holds it at " +
      "the gate and " +
      "refuses it after the cancel's turn; the mutant enters the closure",
  },
  gateHoldsSamples: {
    program:
      {"fibers":[{"id":"f0","daemon":false,"body":[{"s":"sleep","op":"s1",
      "ms":0},{"s":"await","op":"s1"}]}]},
    choices: [
      "sample:0:0", "fire:2", "crash", "kill",
    ],
    baseChoices: [
      "sample:0:0", "fire:2", "crash", "kill",
    ],
    note:
      "the turn for s1's result issues a sample; under the mutant the sample " +
      "waits at the gate for s1's own cause, which waits for the sample, so " +
      "the turn never runs (M7)",
  },
  reattachOnCancel: {
    program:
      {"fibers":[{"id":"f0","daemon":false,"body":[{"s":"sleep","op":"s1",
      "ms":1},{"s":"ensuring","body":[{"s":"await","op":"s1"}],"finalizer":[{
      "s":"call","op":"c1","result":"ok"},{"s":"await","op":"c1"}]}]}]},
    choices: [
      "cancel", "sample:0:0", "sample:4:0", "id:6", "cancel", "sample:11:0",
      "done:8", "done:10", "sample:15:0",
    ],
    baseChoices: [
      "cancel", "sample:0:0", "sample:4:0", "id:6", "cancel", "sample:10:0",
      "done:8", "sample:13:0",
    ],
    note:
      "a second cancel while the compensation's attach is pending: " +
      "the mutant " +
      "issues a second attach command",
  },
  noFreeze: {
    program:
      {"fibers":[{"id":"f0","daemon":false,"body":[{"s":"run","op":"r1",
      "behaviour":"mapAbort"},{"s":"sleep","op":"s1","ms":2},{"s":"await",
      "op":"s1"},{"s":"run","op":"r2","behaviour":"honour","deadline":2}]}]},
    choices: [
      "sample:0:2", "fire:3", "sample:5:2", "end", "ack:2",
    ],
    baseChoices: [
      "sample:0:2", "fire:3", "sample:5:2", "end", "ack:2",
    ],
    note:
      "r1 is aborted when the root exits and maps the abort to an error " +
      "of its own, a retryable failure; base holds it and records a freeze " +
      "before the attempt ends, the mutant returns it at once with no " +
      "freeze event (C18)",
  },
  retryableFirst: {
    program:
      {"fibers":[{"id":"f0","daemon":false,"body":[{"s":"run","op":"r1",
      "behaviour":"ok"},{"s":"run","op":"r2","behaviour":"retryable"},{
      "s":"await","op":"r1"},{"s":"await","op":"r2"}]}]},
    choices: [
      "sample:0:0", "settle:3", "settle:2", "end", "settle:2", "ack:2",
      "sample:5:0", "settle:3", "end",
    ],
    baseChoices: [
      "sample:0:0", "settle:3", "settle:2", "ack:2", "end", "sample:5:0",
      "settle:3", "end",
    ],
    note:
      "r2 fails retryably, then r1 succeeds during the freeze: base proposes " +
      "r1's success before the retryable failure, so it can be acknowledged " +
      "and journaled; the mutant ends the attempt first and r1 runs again " +
      "(M2)",
  },
  cancelCompensation: {
    program:
      {"fibers":[{"id":"f0","daemon":false,"body":[{"s":"sleep","op":"s1",
      "ms":1},{"s":"ensuring","body":[{"s":"await","op":"s1"}],"finalizer":[{
      "s":"call","op":"c1","result":"ok"},{"s":"sleep","op":"s2","ms":0},{
      "s":"race","ops":["c1","s2"]}]}]}]},
    choices: [
      "cancel", "sample:0:0", "sample:4:0", "id:6", "fire:7", "sample:11:0",
    ],
    baseChoices: [
      "cancel", "sample:0:0", "sample:4:0", "id:6", "fire:7", "sample:11:0",
    ],
    note:
      "the compensation loses a race to a 0 ms sleep: base retires the " +
      "attach, the mutant cancels the child (C27)",
  },
  handlerScheduler: {
    program:
      {"fibers":[{"id":"f0","daemon":false,"body":[{"s":"sleep","op":"s1",
      "ms":1},{"s":"sleep","op":"s2","ms":1},{"s":"run","op":"r1",
      "behaviour":"retryable"},{"s":"race","ops":["s1","s2"]}]}]},
    choices: [
      "sample:0:2", "fire:2", "settle:4", "fire:3", "sample:6:2", "end",
      "ack:4",
    ],
    baseChoices: [
      "sample:0:2", "fire:2", "settle:4", "fire:3", "sample:6:2", "end",
      "ack:4",
    ],
    note:
      "r1 fails retryably while s1's turn waits for its sample; base " +
      "freezes at once, so s1 is never delivered in attempt 0; the mutant " +
      "sees the failure only at the next turn, after s1's delivery, the " +
      "race and the root's exit (M8)",
  },
};

/** Replay a witness and return its history. options.mutant selects the
 * mutant (normally `name`); with no mutant the base model runs. */
export const replayWitness = (name, options = {}) => {
  const witness = mutantWitnesses[name];
  const labels = options.mutant ? witness.choices : witness.baseChoices;
  let state = M.initial(witness.program, options);
  for (const label of labels) state = M.step(state, label);
  if (M.choices(state).length > 0) {
    throw new Error(`witness ${name} did not reach a terminal state`);
  }
  return M.history(state);
};
