// Self-test for predicates.mjs. Run: node predicates.test.mjs
// For every predicate: at least one hand-built history it accepts and one
// minimal counterexample it rejects. Every valid base history is also run
// through every predicate, so a predicate that rejects a correct history
// fails here. Exits non-zero on any failure.

import { pathToFileURL } from 'node:url';
import { predicates, pairPredicates, boundaries } from './predicates.mjs';

// ------------------------------------------------------------ builders

const J = (...entries) => entries.map((e, idx) => ({ ...e, idx }));
const C = (c, op, extra = {}) => ({ e: 'cmd', cmd: { c, op, ...extra } });
const S = () => C('run', 'sample');
const N = (of, value) => ({ e: 'notif', of, value });
const ok = (v = null) => ({ ok: v });
const X = () => ({ e: 'cancel' });
const O = (kind) => ({ e: 'output', outcome: { kind } });
const CC = (target, by) => ({ e: 'cmd', cmd: { c: 'cancelCall', target, by } });

const T = {
  turn: (cause, entryIdx) =>
    (entryIdx === undefined ? { t: 'turn', cause } : { t: 'turn', cause, entryIdx }),
  release: (op, cause, fiber = 'f0') => ({ t: 'release', fiber, op, cause }),
  wrapper: (op, cmdIdx) => ({ t: 'wrapper', op, cmdIdx }),
  enter: (op, cmdIdx) => ({ t: 'enter', op, cmdIdx }),
  refuse: (op, cmdIdx) => ({ t: 'refuse', op, cmdIdx }),
  done: (op, cmdIdx, outcome) => ({ t: 'done', op, cmdIdx, outcome }),
  settle: (op, cmdIdx, outcome) => ({ t: 'settle', op, cmdIdx, outcome }),
  propose: (op, cmdIdx, outcome) => ({ t: 'propose', op, cmdIdx, outcome }),
  issue: (cmdIdx, fiber = 'f0') => ({ t: 'issue', fiber, cmdIdx }),
  consume: (entryIdx) => ({ t: 'consume', entryIdx }),
  sample: (cmdIdx, reading, trueTime = reading) =>
    ({ t: 'sample', cmdIdx, reading, trueTime }),
  deliver: (op, value, fiber = 'f0') => ({ t: 'deliver', fiber, op, value }),
  interrupt: (fiber, cause) => ({ t: 'interrupt', fiber, cause }),
  abort: (op, cause) => ({ t: 'abort', op, cause }),
  clock: (L, fiber = 'f0') => ({ t: 'clock', fiber, L }),
  draw: (value, fiber = 'f0') => ({ t: 'draw', fiber, value }),
  violation: (kind) => ({ t: 'violation', kind }),
  freeze: () => ({ t: 'freeze' }),
  warn: (which, runs, tick = 0) => ({ t: 'warn', which, runs, tick }),
  exit: (kind) => ({ t: 'rootExit', outcome: { kind } }),
};

// The first turn: its sample command at sIdx, its result at nIdx.
const first = (sIdx = 0, nIdx = 1, reading = 0, tt = reading) => [
  T.turn('first'), T.issue(sIdx), T.consume(nIdx), T.sample(sIdx, reading, tt)];
// A journal turn's opening for the cause at journal index `cause`: turn, its
// sample issued and applied.
const jturn = (cause, sIdx, nIdx, reading, tt = reading) => [
  T.turn('journal', cause), T.issue(sIdx), T.consume(nIdx),
  T.sample(sIdx, reading, tt)];

const eff = (op, settled, o = {}) => ({
  op, attempt: o.attempt ?? 0, entered: 'entered' in o ? o.entered : true,
  signalAbortedAtEntry: o.abortedAtEntry ?? false, settled,
});

const att = (o) => ({
  n: 0, journalIn: [], effects: [], ...o,
  end: o.end ?? { kind: 'output', at: o.trace.length - 1 },
});
const hist = (program, attempts, outcome = null, children = []) =>
  ({ program, attempts, outcome: outcome && { kind: outcome }, children });
const prog = (f0, f1 = null, daemon = false) => ({
  fibers: [{ id: 'f0', daemon: false, body: f0 },
    ...(f1 ? [{ id: 'f1', daemon, body: f1 }] : [])],
});
const edit = (h, change) => { const c = structuredClone(h); change(c); return c; };
const ret = { s: 'return' };

// ------------------------------------------------------- valid bases

// One run, awaited, then a clock read.
const RUN = hist(
  prog([{ s: 'run', op: 'r1', behaviour: 'ok' }, { s: 'await', op: 'r1' },
    { s: 'clock' }, ret]),
  [att({
    journalOut: J(S(), N(0, ok(0)), C('run', 'r1'), N(2, ok('v')), S(),
      N(4, ok(1)), O('success')),
    trace: [...first(), T.issue(2), T.consume(3), ...jturn(3, 4, 5, 1),
      T.deliver('r1', ok('v')), T.clock(1), T.exit('success')],
    effects: [eff('r1', 'ok')],
  })], 'success');

// Two runs whose results both arrive before the first is delivered.
const TWO_RUNS = hist(
  prog([{ s: 'run', op: 'r1', behaviour: 'ok' },
    { s: 'run', op: 'r2', behaviour: 'ok' },
    { s: 'await', op: 'r1' }, { s: 'await', op: 'r2' }, ret]),
  [att({
    journalOut: J(S(), N(0, ok(0)), C('run', 'r1'), C('run', 'r2'),
      N(2, ok('a')), N(3, ok('b')), S(), N(6, ok(1)), S(), N(8, ok(2)),
      O('success')),
    trace: [...first(), T.issue(2), T.issue(3), T.consume(4),
      T.turn('journal', 4), T.issue(6), T.consume(5), T.consume(7),
      T.sample(6, 1), T.deliver('r1', ok('a')),
      ...jturn(5, 8, 9, 2), T.deliver('r2', ok('b')), T.exit('success')],
    effects: [eff('r1', 'ok'), eff('r2', 'ok')],
  })], 'success');

// A crash after the run's closure settled but before its result was
// journaled, then a replay that runs it again.
const CRASH_PROGRAM = prog([{ s: 'draw' }, { s: 'run', op: 'r1', behaviour: 'ok' },
  { s: 'await', op: 'r1' }, ret]);
const CRASH_J0 = J(S(), N(0, ok(0)), C('run', 'r1'));
const CRASH_J1 = J(S(), N(0, ok(0)), C('run', 'r1'), N(2, ok('v')), S(),
  N(4, ok(5)), O('success'));
const CRASH_T1 = [...first(), T.draw(7), T.issue(2), T.consume(3),
  ...jturn(3, 4, 5, 5), T.deliver('r1', ok('v')), T.exit('success')];
const CRASH = hist(CRASH_PROGRAM, [
  att({ journalOut: CRASH_J0, trace: [...first(), T.draw(7), T.issue(2)],
    effects: [eff('r1', 'ok')], end: { kind: 'crashed', at: 5 } }),
  att({ n: 1, journalIn: CRASH_J0, journalOut: CRASH_J1, trace: CRASH_T1,
    effects: [eff('r1', 'ok', { attempt: 1 })] }),
], 'success');

// The same program run live once, with the same inputs.
const LIVE = hist(CRASH_PROGRAM, [att({ journalOut: CRASH_J1, trace: CRASH_T1,
  effects: [eff('r1', 'ok')] })], 'success');

// Restate's abort timeout during a run that honours its signal.
const ENDED = hist(
  prog([{ s: 'run', op: 'r1', behaviour: 'honour' }, { s: 'await', op: 'r1' }, ret]),
  [att({ journalOut: CRASH_J0,
    trace: [...first(), T.issue(2), T.abort('r1', 'ended'),
      T.interrupt('f0', 'closing')],
    effects: [eff('r1', 'aborted')], end: { kind: 'ended', at: 4 } }),
  att({ n: 1, journalIn: CRASH_J0, journalOut: CRASH_J1,
    trace: [...first(), T.issue(2), T.consume(3), ...jturn(3, 4, 5, 5),
      T.deliver('r1', ok('v')), T.exit('success')],
    effects: [eff('r1', 'ok', { attempt: 1 })] }),
  ], 'success');

// A retryable closure failure: freeze, retry, success.
const FREEZE = hist(
  prog([{ s: 'run', op: 'r1', behaviour: 'retryable' }, { s: 'await', op: 'r1' }, ret]),
  [att({ journalOut: CRASH_J0, trace: [...first(), T.issue(2), T.freeze()],
    effects: [eff('r1', 'retryable')], end: { kind: 'retry', at: 5 } }),
  att({ n: 1, journalIn: CRASH_J0, journalOut: CRASH_J1,
    trace: [...first(), T.issue(2), T.consume(3), ...jturn(3, 4, 5, 5),
      T.deliver('r1', ok('v')), T.exit('success')],
    effects: [eff('r1', 'ok', { attempt: 1 })] }),
  ], 'success');

// A call whose child answers 409; the root fails terminally.
const CALL409 = hist(
  prog([{ s: 'call', op: 'c1', result: 'terminal' }, { s: 'await', op: 'c1' },
    { s: 'fail', kind: 'terminal' }]),
  [att({
    journalOut: J(S(), N(0, ok(0)), C('call', 'c1'), N(2, { invocationId: 'k1' }),
      N(2, { terminal: '409' }), S(), N(5, ok(1)), O('terminal')),
    trace: [...first(), T.issue(2), T.consume(3), T.consume(4), ...jturn(4, 5, 6, 1),
      T.deliver('c1', { terminal: '409' }), T.exit('terminal')],
  })], 'terminal',
  [{ key: null, viaCmd: 2, attempt: 0, kind: 'call', ran: 1, cancelled: false, killed: false }]);

// The root returns while a forked fiber awaits a call: closing interrupts the
// fiber, waits for the call's id and cancels it.
const CLOSING = hist(
  prog([{ s: 'fork', fiber: 'f1' }, ret],
    [{ s: 'call', op: 'c1', result: 'ok' }, { s: 'await', op: 'c1' }]),
  [att({
    journalOut: J(S(), N(0, ok(0)), C('call', 'c1'), N(2, { invocationId: 'k1' }),
      CC(2, 'executor'), O('success')),
    trace: [...first(), T.issue(2, 'f1'), T.exit('success'),
      T.interrupt('f1', 'closing'), T.release('c1', 'interrupt', 'f1'),
      T.consume(3), T.issue(4)],
  })], 'success',
  [{ key: null, viaCmd: 2, attempt: 0, kind: 'call', ran: 1, cancelled: true, killed: false }]);

// A cancellation while the root sleeps inside `ensuring`; the finalizer's
// call is a send under key <invocation id>:3, attached, and delivered.
const CANCEL_PROGRAM = prog([{ s: 'ensuring',
  body: [{ s: 'sleep', op: 's1', ms: 2 }, { s: 'await', op: 's1' }],
  finalizer: [{ s: 'call', op: 'c1', result: 'ok' }, { s: 'await', op: 'c1' }] }, ret]);
const KEY = 'inv-1:3';
const COMP_CHILD = [{ key: KEY, viaCmd: 6, attempt: 0, kind: 'send', ran: 1,
  cancelled: false, killed: false }];
const CANCEL_HEAD_J = [S(), N(0, ok(0)), C('sleep', 's1', { ms: 2 }), X(), S(),
  N(4, ok(1)), C('send', 'c1', { key: KEY }), N(6, { invocationId: 'k1' }),
  C('attach', 'c1', { target: KEY })];
const CANCEL_HEAD_T = [...first(), T.issue(2), T.consume(3), ...jturn(3, 4, 5, 1),
  T.interrupt('f0', 'cancel'), T.release('s1', 'interrupt'), T.issue(6),
  T.consume(7), T.issue(8)];
const CANCEL = hist(CANCEL_PROGRAM, [att({
  journalOut: J(...CANCEL_HEAD_J, N(8, ok('done')), S(), N(10, ok(2)), O('cancelled')),
  trace: [...CANCEL_HEAD_T, T.consume(9), ...jturn(9, 10, 11, 2),
    T.deliver('c1', ok('done')), T.exit('cancelled')],
})], 'cancelled', COMP_CHILD);

// As CANCEL, with a second cancel signal while the root unwinds.
const TWO_CANCEL = hist(CANCEL_PROGRAM, [att({
  journalOut: J(...CANCEL_HEAD_J, X(), N(8, ok('done')), S(), N(11, ok(2)), S(),
    N(13, ok(3)), O('cancelled')),
  trace: [...CANCEL_HEAD_T, T.consume(9), T.turn('journal', 9), T.issue(11),
    T.consume(10), T.consume(12), T.sample(11, 2), ...jturn(10, 13, 14, 3),
    T.deliver('c1', ok('done')), T.exit('cancelled')],
})], 'cancelled', COMP_CHILD);

// A cancel signal journaled after a buffered result, consumed while that
// result's turn waits for its sample.
const ORDER_PROGRAM = prog([{ s: 'run', op: 'r1', behaviour: 'ok' },
  { s: 'await', op: 'r1' }, { s: 'sleep', op: 's1', ms: 2 }, { s: 'await', op: 's1' }, ret]);
const ORDER = hist(ORDER_PROGRAM, [att({
  journalOut: J(S(), N(0, ok(0)), C('run', 'r1'), N(2, ok('v')), X(), S(),
    N(5, ok(1)), C('sleep', 's1', { ms: 2 }), S(), N(8, ok(1)), O('cancelled')),
  trace: [...first(), T.issue(2), T.consume(3), T.turn('journal', 3), T.issue(5),
    T.consume(4), T.consume(6), T.sample(5, 1), T.deliver('r1', ok('v')),
    T.issue(7), ...jturn(4, 8, 9, 1), T.interrupt('f0', 'cancel'),
    T.release('s1', 'interrupt'), T.exit('cancelled')],
  effects: [eff('r1', 'ok')],
})], 'cancelled');

// A run with a 1-tick deadline that fires first; the run honours the abort.
const DEADLINE_PROGRAM = prog([{ s: 'run', op: 'r1', behaviour: 'honour', deadline: 1 },
  { s: 'await', op: 'r1' }, { s: 'fail', kind: 'terminal' }]);
const DEADLINE_J = J(S(), N(0, ok(0)), C('run', 'r1'), C('sleep', 'deadline', { ms: 1 }),
  N(3, ok()), N(2, { terminal: 'aborted' }), S(), N(6, ok(2)), O('terminal'));
const DEADLINE_T = [...first(), T.issue(2), T.issue(3), T.consume(4),
  T.abort('r1', 'deadline'), T.consume(5), ...jturn(5, 6, 7, 2),
  T.deliver('r1', { terminal: 'aborted' }), T.exit('terminal')];
const DEADLINE = hist(DEADLINE_PROGRAM, [att({ journalOut: DEADLINE_J,
  trace: DEADLINE_T, effects: [eff('r1', 'aborted')] })], 'terminal');

// The deadline fires, then a crash loses the run's result; the replay
// re-aborts and the wrapper refuses to enter the closure.
const REABORT_J0 = DEADLINE_J.slice(0, 5);
const REABORT = hist(DEADLINE_PROGRAM, [
  att({ journalOut: REABORT_J0, trace: DEADLINE_T.slice(0, 8),
    effects: [eff('r1', null)], end: { kind: 'crashed', at: 7 } }),
  att({ n: 1, journalIn: REABORT_J0, journalOut: DEADLINE_J, trace: DEADLINE_T,
    effects: [eff('r1', 'aborted', { attempt: 1, entered: false, abortedAtEntry: true })] }),
], 'terminal');

// A run loses a race to a sleep, is retained and aborted, ignores the abort,
// and closing waits for its result. Warnings name it while it holds closing.
const RETAINED = hist(
  prog([{ s: 'run', op: 'r1', behaviour: 'ignoreOk' }, { s: 'sleep', op: 's1', ms: 1 },
    { s: 'race', ops: ['r1', 's1'] }, ret]),
  [att({
    journalOut: J(S(), N(0, ok(0)), C('run', 'r1'), C('sleep', 's1', { ms: 1 }),
      N(3, ok()), S(), N(5, ok(1)), N(2, ok('late')), O('success')),
    trace: [...first(), T.issue(2), T.issue(3), T.consume(4), ...jturn(4, 5, 6, 1),
      T.deliver('s1', ok()), T.interrupt('f0', 'race'), T.release('r1', 'race'),
      T.abort('r1', 'interrupt'),
      T.exit('success'), T.warn(1, ['r1'], 3), T.warn(2, ['r1'], 9), T.consume(7)],
    effects: [eff('r1', 'ok')],
  })], 'success');

// As RETAINED, but the run's closure had not started: the wrapper refuses it.
const UNSTARTED = edit(RETAINED, (h) => {
  h.attempts[0].journalOut[7].value = { terminal: 'aborted' };
  h.attempts[0].effects = [eff('r1', 'aborted', { entered: false, abortedAtEntry: true })];
  h.attempts[0].trace = h.attempts[0].trace.filter((e) => e.t !== 'warn');
  h.attempts[0].end.at -= 2;
});

// Two 2 ms sleeps issued in one turn at L = 0; host clock stuck at 0 while
// true time advances by 2.
const SLEEPS = hist(
  prog([{ s: 'sleep', op: 's1', ms: 2 }, { s: 'sleep', op: 's2', ms: 2 },
    { s: 'await', op: 's1' }, { s: 'await', op: 's2' }, { s: 'clock' }, ret]),
  [att({
    journalOut: J(S(), N(0, ok(0)), C('sleep', 's1', { ms: 2 }), C('sleep', 's2', { ms: 2 }),
      N(2, ok()), S(), N(3, ok()), N(5, ok(0)), S(), N(8, ok(0)), O('success')),
    trace: [...first(), T.issue(2), T.issue(3), T.consume(4), T.turn('journal', 4),
      T.issue(5), T.consume(6), T.consume(7), T.sample(5, 0, 2), T.deliver('s1', ok()),
      ...jturn(6, 8, 9, 0, 2), T.deliver('s2', ok()), T.clock(2), T.exit('success')],
  })], 'success');

// A 3 ms sleep as a chain of links 2 and 1.
const CHAIN = hist(
  prog([{ s: 'sleep', op: 's1', ms: 3 }, { s: 'await', op: 's1' }, { s: 'clock' }, ret]),
  [att({
    journalOut: J(S(), N(0, ok(0)), C('sleep', 's1', { ms: 2 }), N(2, ok()), S(),
      N(4, ok(2)), C('sleep', 's1', { ms: 1 }), N(6, ok()), S(), N(8, ok(3)), O('success')),
    trace: [...first(), T.issue(2), T.consume(3), ...jturn(3, 4, 5, 2), T.issue(6),
      T.consume(7), ...jturn(7, 8, 9, 3), T.deliver('s1', ok()), T.clock(3), T.exit('success')],
  })], 'success');

// A run wins a race against a 2 ms sleep; the released sleep adds nothing.
const RACE_SLEEP = hist(
  prog([{ s: 'run', op: 'r1', behaviour: 'ok' }, { s: 'sleep', op: 's1', ms: 2 },
    { s: 'race', ops: ['r1', 's1'] }, { s: 'clock' }, ret]),
  [att({
    journalOut: J(S(), N(0, ok(0)), C('run', 'r1'), C('sleep', 's1', { ms: 2 }),
      N(2, ok('v')), S(), N(5, ok(0)), O('success')),
    trace: [...first(), T.issue(2), T.issue(3), T.consume(4), ...jturn(4, 5, 6, 0),
      T.deliver('r1', ok('v')), T.interrupt('f0', 'race'), T.release('s1', 'race'),
      T.clock(0), T.exit('success')],
    effects: [eff('r1', 'ok')],
  })], 'success');

// Suspension while a sleep is pending, after a run's result was journaled.
const SUSP = hist(
  prog([{ s: 'run', op: 'r1', behaviour: 'ok' }, { s: 'await', op: 'r1' },
    { s: 'sleep', op: 's1', ms: 2 }, { s: 'await', op: 's1' }, ret]),
  [att({
    journalOut: J(S(), N(0, ok(0)), C('run', 'r1'), N(2, ok('v')), S(), N(4, ok(1)),
      C('sleep', 's1', { ms: 2 })),
    trace: [...first(), T.issue(2), T.consume(3), ...jturn(3, 4, 5, 1),
      T.deliver('r1', ok('v')), T.issue(6)],
    effects: [eff('r1', 'ok')], end: { kind: 'suspended', at: 11 },
  })]);

// A kill during a run.
const KILLED = hist(RUN.program, [att({ journalOut: J(S(), N(0, ok(0)), C('run', 'r1')),
  trace: [...first(), T.issue(2)], effects: [eff('r1', null)],
  end: { kind: 'killed', at: 4 } })]);

// A root blocked with nothing pending.
const BLOCKED = hist(prog([{ s: 'await', op: 'nothing' }]), [att({
  journalOut: J(S(), N(0, ok(0)), O('defect')),
  trace: [...first(), T.violation('blocked'), T.exit('defect')],
})], 'defect');

// A cancellation while the root awaits a run inside an uninterruptible
// region: the run is not released, and is delivered after the interrupt.
const UNINT = hist(
  prog([{ s: 'uninterruptible', body: [{ s: 'run', op: 'r1', behaviour: 'ok' }] },
    { s: 'await', op: 'r1' }, ret]),
  [att({
    journalOut: J(S(), N(0, ok(0)), C('run', 'r1'), X(), S(), N(4, ok(1)),
      N(2, ok('v')), S(), N(7, ok(2)), O('cancelled')),
    trace: [...first(), T.issue(2), T.consume(3), ...jturn(3, 4, 5, 1),
      T.interrupt('f0', 'cancel'), T.consume(6), ...jturn(6, 7, 8, 2),
      T.deliver('r1', ok('v')), T.exit('cancelled')],
    effects: [eff('r1', 'ok')],
  })], 'cancelled');

// --- histories for the revised format (release, entryIdx, entered: null,
// retryable root exit, mismatch)

// The race loser's result is consumed while the winner's turn waits for its
// sample, then dropped at the head of the queue: no turn, no sample.
const DROP = hist(RACE_SLEEP.program, [att({
  journalOut: J(S(), N(0, ok(0)), C('run', 'r1'), C('sleep', 's1', { ms: 2 }),
    N(2, ok('v')), S(), N(3, ok()), N(5, ok(0)), O('success')),
  trace: [...first(), T.issue(2), T.issue(3), T.consume(4), T.turn('journal', 4),
    T.issue(5), T.consume(6), T.consume(7), T.sample(5, 0), T.deliver('r1', ok('v')),
    T.interrupt('f0', 'race'), T.release('s1', 'race'), T.clock(0), T.exit('success')],
  effects: [eff('r1', 'ok')],
})], 'success');

// A kill while the wrapper still holds the closure at the entry gate.
const HELD = edit(KILLED, (h) => {
  h.attempts[0].effects = [eff('r1', null, { entered: null })];
});

// A kill cuts the first cancel's turn short: before its sample is applied,
// and just after it.
const CUT_BEFORE_SAMPLE = hist(CANCEL_PROGRAM, [att({
  journalOut: J(...CANCEL_HEAD_J.slice(0, 5)),
  trace: [...first(), T.issue(2), T.consume(3), T.turn('journal', 3), T.issue(4)],
  end: { kind: 'killed', at: 7 },
})]);
const CUT_AFTER_SAMPLE = hist(CANCEL_PROGRAM, [att({
  journalOut: J(...CANCEL_HEAD_J.slice(0, 6)),
  trace: [...first(), T.issue(2), T.consume(3), ...jturn(3, 4, 5, 1)],
  end: { kind: 'killed', at: 9 },
})]);

// After the crash, the replay rebuilds the deadline and its terminal abort
// is journaled, with no effect entry for the run.
const REABORT_NO_EFFECT = edit(REABORT, (h) => { h.attempts[1].effects = []; });

// The root fails retryably: the attempt ends "retry" with no Output.
const RETRY_ROOT = hist(prog([{ s: 'fail', kind: 'retryable' }]), [att({
  journalOut: J(S(), N(0, ok(0))),
  trace: [...first(), T.exit('retryable')],
  end: { kind: 'retry', at: 4 },
})]);

// --- exit releases: an unawaited operation is a forked child of its fiber,
// interrupted when that fiber completes.

// The root returns with an unawaited run: it is aborted and retained, and
// Output waits for its result.
const EXIT_RUN = hist(prog([{ s: 'run', op: 'r1', behaviour: 'ignoreOk' }, ret]), [att({
  journalOut: J(S(), N(0, ok(0)), C('run', 'r1'), N(2, ok('late')), O('success')),
  trace: [...first(), T.issue(2), T.exit('success'), T.release('r1', 'exit'),
    T.abort('r1', 'interrupt'), T.consume(3)],
  effects: [eff('r1', 'ok')],
})], 'success');

// The root returns with an unawaited call: closing waits for its id and
// cancels it.
const EXIT_CALL = hist(prog([{ s: 'call', op: 'c1', result: 'ok' }, ret]), [att({
  journalOut: J(S(), N(0, ok(0)), C('call', 'c1'), N(2, { invocationId: 'k1' }),
    CC(2, 'executor'), O('success')),
  trace: [...first(), T.issue(2), T.exit('success'), T.release('c1', 'exit'),
    T.consume(3), T.issue(4)],
})], 'success',
[{ key: null, viaCmd: 2, attempt: 0, kind: 'call', ran: 1, cancelled: true, killed: false }]);

// The exit abort, then a crash; the replay rebuilds it and refuses the run.
const EXIT_J0 = J(S(), N(0, ok(0)), C('run', 'r1'));
const EXIT_T = [...first(), T.issue(2), T.exit('success'), T.release('r1', 'exit'),
  T.abort('r1', 'interrupt')];
const EXIT_REABORT = hist(EXIT_RUN.program, [
  att({ journalOut: EXIT_J0, trace: EXIT_T, effects: [eff('r1', null)],
    end: { kind: 'crashed', at: 7 } }),
  att({ n: 1, journalIn: EXIT_J0,
    journalOut: J(...EXIT_J0, N(2, { terminal: 'aborted' }), O('success')),
    trace: [...EXIT_T, T.consume(3)],
    effects: [eff('r1', 'aborted', { attempt: 1, entered: false, abortedAtEntry: true })] }),
], 'success');

// Closing interrupts a forked fiber's run, then a crash; the replay reaches
// the same exit, re-aborts the run and refuses it.
const CLOSE_J0 = J(S(), N(0, ok(0)), C('run', 'r1'));
const CLOSE_T = [...first(), T.issue(2, 'f1'), T.exit('success'),
  T.interrupt('f1', 'closing'), T.release('r1', 'interrupt', 'f1'),
  T.abort('r1', 'interrupt')];
const CLOSE_REABORT = hist(prog([{ s: 'fork', fiber: 'f1' }, ret],
  [{ s: 'run', op: 'r1', behaviour: 'ignoreOk' }, { s: 'await', op: 'r1' }]), [
  att({ journalOut: CLOSE_J0, trace: CLOSE_T, effects: [eff('r1', null)],
    end: { kind: 'crashed', at: 8 } }),
  att({ n: 1, journalIn: CLOSE_J0,
    journalOut: J(...CLOSE_J0, N(2, { terminal: 'aborted' }), O('success')),
    trace: [...CLOSE_T, T.consume(3)],
    effects: [eff('r1', 'aborted', { attempt: 1, entered: false, abortedAtEntry: true })] }),
], 'success');

// --- closure lifecycle events

// Inserts events at a trace position and keeps end.at on the last event.
const withEvents = (h, pos, events, a = 0) => edit(h, (c) => {
  const at = c.attempts[a];
  at.trace.splice(pos, 0, ...events);
  at.end.at += events.length;
});

// Both runs enter before any cause is consumed (gate passes).
const GATE_OK = withEvents(TWO_RUNS, 6, [T.wrapper('r1', 2), T.enter('r1', 2),
  T.wrapper('r2', 3), T.enter('r2', 3), T.settle('r1', 2, 'ok'), T.propose('r1', 2, 'ok'),
  T.settle('r2', 3, 'ok'), T.propose('r2', 3, 'ok')]);
// r2's closure enters after r1's result is consumed and before r1's turn
// has applied its sample and delivered it.
const GATE_BAD = edit(withEvents(TWO_RUNS, 6, [T.wrapper('r1', 2), T.enter('r1', 2),
  T.settle('r1', 2, 'ok'), T.propose('r1', 2, 'ok'), T.wrapper('r2', 3)]), (h) => {
  const a = h.attempts[0];
  a.trace.splice(12, 0, T.enter('r2', 3), T.settle('r2', 3, 'ok'), T.propose('r2', 3, 'ok'));
  a.end.at += 3;
});

// The cancellation's turn's sample passes the gate at once, although a
// cancel signal is consumed right after (ORDER's second turn).
const SAMPLE_OK = withEvents(ORDER, 8, [T.wrapper('sample:5', 5), T.enter('sample:5', 5)]);
// The sample's closure waits while the race consumes the cancel signal.
const SAMPLE_WAIT = edit(withEvents(ORDER, 8, [T.wrapper('sample:5', 5)]), (h) => {
  h.attempts[0].trace.splice(10, 0, T.enter('sample:5', 5));
  h.attempts[0].end.at += 1;
});
// The attempt writes output with a sample's wrapper still held.
const SAMPLE_HELD = withEvents(RUN, 8, [T.wrapper('sample:4', 4)]);

// Two runs: r1 succeeds, r2 fails retryably; freeze, r1's success is proposed
// before r2's retryable failure, and the attempt is retried.
const RETRY2 = hist(
  prog([{ s: 'run', op: 'r1', behaviour: 'ok' }, { s: 'run', op: 'r2', behaviour: 'retryable' },
    { s: 'await', op: 'r1' }, { s: 'await', op: 'r2' }, ret]),
  [att({
    journalOut: J(S(), N(0, ok(0)), C('run', 'r1'), C('run', 'r2')),
    trace: [...first(), T.issue(2), T.issue(3), T.wrapper('r1', 2), T.enter('r1', 2),
      T.wrapper('r2', 3), T.enter('r2', 3), T.settle('r1', 2, 'ok'),
      T.settle('r2', 3, 'retryable'), T.freeze(), T.propose('r1', 2, 'ok'),
      T.propose('r2', 3, 'retryable')],
    effects: [eff('r1', 'ok'), eff('r2', 'retryable')],
    end: { kind: 'retry', at: 14 },
  })]);
const RETRY_NO_FREEZE = edit(RETRY2, (h) => {
  const a = h.attempts[0];
  a.trace = a.trace.filter((e) => e.t !== 'freeze');
  a.end.at -= 1;
});
const RETRY_ENTERS = withEvents(RETRY2, 12, [T.wrapper('r3', 4), T.enter('r3', 4)]);
const RETRY_BAD_ORDER = edit(RETRY2, (h) => {
  const t = h.attempts[0].trace;
  [t[13], t[14]] = [t[14], t[13]];
});
const RETRY_DELIVERS = withEvents(RETRY2, 12, [T.deliver('r1', ok('a'))]);
const RETRY_EARLY_FREEZE = edit(RETRY2, (h) => {
  const t = h.attempts[0].trace;
  [t[11], t[12]] = [t[12], t[11]];
});

// --- fixes after the first model run

// The live attempt runs r1's closure and crashes after its result is
// journaled; the replay never asks for the closure again. Lifecycle events
// differ between the two, which S1 must not compare.
const LIFE_REPLAY = hist(CRASH_PROGRAM, [
  att({ journalOut: CRASH_J1.slice(0, 4),
    trace: [...first(), T.draw(7), T.issue(2), T.wrapper('r1', 2), T.enter('r1', 2),
      T.done('r1', 2, 'ok'), T.settle('r1', 2, 'ok'), T.propose('r1', 2, 'ok'), T.consume(3)],
    effects: [eff('r1', 'ok')], end: { kind: 'crashed', at: 11 } }),
  att({ n: 1, journalIn: CRASH_J1.slice(0, 4), journalOut: CRASH_J1, trace: CRASH_T1 }),
], 'success');

// r2 fails retryably first; r1's success settles during the freeze and is
// proposed before the retryable failure.
const RETRY_LATE_OK = edit(RETRY2, (h) => {
  const a = h.attempts[0];
  a.trace = [...first(), T.issue(2), T.issue(3), T.wrapper('r1', 2), T.enter('r1', 2),
    T.wrapper('r2', 3), T.enter('r2', 3), T.settle('r2', 3, 'retryable'), T.freeze(),
    T.settle('r1', 2, 'ok'), T.propose('r1', 2, 'ok'), T.propose('r2', 3, 'retryable')];
  a.end.at = a.trace.length - 1;
});
const RETRY_LATE_BAD = edit(RETRY_LATE_OK, (h) => {
  const t = h.attempts[0].trace;
  [t[13], t[14]] = [t[14], t[13]];
});

// A kill after a sample's closure was entered, and one with the sample's
// wrapper still held.
const SAMPLE_KILLED_OK = hist(RUN.program, [att({ journalOut: J(S()),
  trace: [T.turn('first'), T.issue(0), T.wrapper('sample:0', 0), T.enter('sample:0', 0)],
  end: { kind: 'killed', at: 3 } })]);
const SAMPLE_KILLED_HELD = edit(SAMPLE_KILLED_OK, (h) => {
  h.attempts[0].trace.pop();
  h.attempts[0].end.at = 2;
});

// r1's closure completes and the executor learns of it at once; and one
// where the settlement waits past the next turn's command.
const DONE_OK = withEvents(RUN, 5, [T.wrapper('r1', 2), T.enter('r1', 2),
  T.done('r1', 2, 'ok'), T.settle('r1', 2, 'ok'), T.propose('r1', 2, 'ok')]);
const DONE_HELD = withEvents(withEvents(RUN, 5, [T.wrapper('r1', 2), T.enter('r1', 2),
  T.done('r1', 2, 'ok')]), 11, [T.settle('r1', 2, 'ok'), T.propose('r1', 2, 'ok')]);

// Two runs fail retryably: r1 completes first, but the executor freezes on
// r2's settlement.
const TWO_RETRY = hist(
  prog([{ s: 'run', op: 'r1', behaviour: 'retryable' }, { s: 'run', op: 'r2', behaviour: 'retryable' },
    { s: 'await', op: 'r1' }, { s: 'await', op: 'r2' }, ret]),
  [att({
    journalOut: J(S(), N(0, ok(0)), C('run', 'r1'), C('run', 'r2')),
    trace: [...first(), T.issue(2), T.issue(3), T.wrapper('r1', 2), T.enter('r1', 2),
      T.wrapper('r2', 3), T.enter('r2', 3), T.done('r1', 2, 'retryable'),
      T.settle('r1', 2, 'retryable'), T.freeze(), T.done('r2', 3, 'retryable'),
      T.settle('r2', 3, 'retryable'), T.propose('r1', 2, 'retryable'),
      T.propose('r2', 3, 'retryable')],
    effects: [eff('r1', 'retryable'), eff('r2', 'retryable')],
  })]);
TWO_RETRY.attempts[0].end = { kind: 'retry', at: TWO_RETRY.attempts[0].trace.length - 1 };
const TWO_RETRY_BAD = edit(TWO_RETRY, (h) => {
  h.attempts[0].trace = [...first(), T.issue(2), T.issue(3), T.wrapper('r1', 2), T.enter('r1', 2),
    T.wrapper('r2', 3), T.enter('r2', 3), T.done('r1', 2, 'retryable'),
    T.done('r2', 3, 'retryable'), T.settle('r2', 3, 'retryable'), T.freeze(),
    T.settle('r1', 2, 'retryable'), T.propose('r1', 2, 'retryable'),
    T.propose('r2', 3, 'retryable')];
});

// --- fixes after the first exhaustive runs

// The root returns with r1 running; r1 completes inside that turn, and the
// executor learns of it once the turn's synchronous work (exit, release,
// abort) is done. One with a closing turn between the done and its settle.
const DONE_SAME_TURN = edit(EXIT_RUN, (h) => {
  const a = h.attempts[0];
  a.trace = [...first(), T.issue(2), T.wrapper('r1', 2), T.enter('r1', 2), T.done('r1', 2, 'ok'),
    T.exit('success'), T.release('r1', 'exit'), T.abort('r1', 'interrupt'),
    T.settle('r1', 2, 'ok'), T.propose('r1', 2, 'ok'), T.consume(3)];
  a.end.at = a.trace.length - 1;
});
const DONE_NEXT_TURN = withEvents(DONE_SAME_TURN, 8, [T.turn('local')]);

// Two cancel signals journaled while attempt 0 had crashed; the replay
// observes the first, and the SDK's cancel of c1 lands after the second
// signal's entry. One where the SDK cancels c1 again on the second signal.
const RECANCEL_PROGRAM = prog([{ s: 'call', op: 'c1', result: 'ok' }, { s: 'await', op: 'c1' },
  { s: 'sleep', op: 's1', ms: 2 }, { s: 'await', op: 's1' }, ret]);
const RECANCEL_J0 = J(S(), N(0, ok(0)), C('call', 'c1'), N(2, { invocationId: 'k1' }),
  N(2, ok('r')), S(), N(5, ok(1)), C('sleep', 's1', { ms: 2 }), X(), X());
const RECANCEL_T0 = [...first(), T.issue(2), T.consume(3), T.consume(4), ...jturn(4, 5, 6, 1),
  T.deliver('c1', ok('r')), T.issue(7)];
const RECANCEL_CHILD = [{ key: null, viaCmd: 2, attempt: 0, kind: 'call', ran: 1, cancelled: true, killed: false }];
const RECANCEL_OK = hist(RECANCEL_PROGRAM, [
  att({ journalOut: RECANCEL_J0, trace: RECANCEL_T0, end: { kind: 'crashed', at: 12 } }),
  att({ n: 1, journalIn: RECANCEL_J0,
    journalOut: [...RECANCEL_J0, ...J(...Array(10).fill(null), CC(2, 'sdk'), S(), N(11, ok(2)),
      O('cancelled')).slice(10)],
    trace: [...RECANCEL_T0, T.consume(8), T.turn('journal', 8), T.issue(11), T.consume(9),
      T.consume(12), T.sample(11, 2), T.interrupt('f0', 'cancel'), T.release('s1', 'interrupt'),
      T.exit('cancelled')] }),
], 'cancelled', RECANCEL_CHILD);
const RECANCEL_BAD = edit(RECANCEL_OK, (h) => {
  const a = h.attempts[1];
  a.journalOut = [...RECANCEL_J0, ...J(...Array(10).fill(null), S(), N(10, ok(2)), CC(2, 'sdk'),
    O('cancelled')).slice(10)];
  a.trace = [...RECANCEL_T0, T.consume(8), T.turn('journal', 8), T.issue(10), T.consume(9),
    T.consume(11), T.sample(10, 2), T.interrupt('f0', 'cancel'), T.release('s1', 'interrupt'),
    T.exit('cancelled')];
  a.end.at = a.trace.length - 1;
});

const VALID = { DONE_SAME_TURN, RECANCEL_OK, LIFE_REPLAY, RETRY_LATE_OK, SAMPLE_KILLED_OK, DONE_OK, TWO_RETRY, GATE_OK, SAMPLE_OK, RETRY2, CLOSE_REABORT, EXIT_RUN, EXIT_CALL, EXIT_REABORT, DROP, HELD, CUT_BEFORE_SAMPLE, CUT_AFTER_SAMPLE,
  REABORT_NO_EFFECT, RETRY_ROOT, UNINT, RUN, TWO_RUNS, CRASH, LIVE, ENDED, FREEZE, CALL409, CLOSING,
  CANCEL, TWO_CANCEL, ORDER, DEADLINE, REABORT, RETAINED, UNSTARTED, SLEEPS,
  CHAIN, RACE_SLEEP, SUSP, KILLED, BLOCKED };

// ------------------------------------------------- counterexamples

const tr = (h, a = 0) => h.attempts[a].trace;
const setTrace = (h, trace, a = 0) => edit(h, (c) => {
  c.attempts[a].trace = trace;
  c.attempts[a].end.at = trace.length - 1;
});

const CASES = {
  // The replay draws 8 where the live attempt drew 7 under the same inputs.
  S1: [CRASH, edit(CRASH, (h) => { h.attempts[1].trace[4] = T.draw(8); })],
  // The replay issues the turn's sample before the journal's run command.
  S2: [CRASH, edit(CRASH, (h) => {
    const t = h.attempts[1].trace;
    [t[5], t[8]] = [t[8], t[5]];
  })],
  // The live attempt records a violation at position 4; the replay does not.
  S3: [CRASH, edit(CRASH, (h) => { h.attempts[0].trace[4] = T.violation('other'); })],
  // Both buffered results delivered in one turn.
  S4: [TWO_RUNS, edit(TWO_RUNS, (h) => {
    const a = h.attempts[0];
    a.journalOut = a.journalOut.slice(0, 8).concat([{ ...O('success'), idx: 8 }]);
    a.trace = [...a.trace.slice(0, 13), T.deliver('r2', ok('b')), T.exit('success')];
    a.end.at = a.trace.length - 1;
  })],
  // A blocked-handler violation while the run's result is still awaited.
  S6: [BLOCKED, setTrace(RUN, [...first(), T.issue(2), T.violation('blocked')])],
  // The first journal turn delivers r2 although r1 is at the head of the queue.
  S7: [TWO_RUNS, edit(TWO_RUNS, (h) => {
    const t = h.attempts[0].trace;
    t[12] = T.deliver('r2', ok('b'));
    t[17] = T.deliver('r1', ok('a'));
  })],
  // A second clock read goes backwards.
  'S8.P2': [SLEEPS, edit(SLEEPS, (h) => {
    const t = h.attempts[0].trace;
    t.splice(19, 0, T.clock(1));
    h.attempts[0].end.at += 1;
  })],
  // The chain's links sum to 4 for a 3 ms sleep.
  'S8.P3P9': [CHAIN, edit(CHAIN, (h) => { h.attempts[0].journalOut[6].cmd.ms = 2; })],
  // L reads 0 after a sample of 1 was applied.
  'S8.P4': [RUN, edit(RUN, (h) => { h.attempts[0].trace[11] = T.clock(0); })],
  // L reads 3: above true time 2 + E 0 + lead 0.
  'S8.P5': [SLEEPS, edit(SLEEPS, (h) => { h.attempts[0].trace[18] = T.clock(3); })],
  // Two overlapping 2 ms sleeps credited as 4 ms.
  'S8.P6': [SLEEPS, edit(SLEEPS, (h) => { h.attempts[0].trace[18] = T.clock(4); })],
  // The result is delivered before its turn's sample is applied.
  'S8.P7': [RUN, edit(RUN, (h) => {
    const t = h.attempts[0].trace;
    [t[9], t[10]] = [t[10], t[9]];
  })],
  // The released sleep is credited: L reads 2 with every sample at 0.
  'S8.P8': [RACE_SLEEP, edit(RACE_SLEEP, (h) => { h.attempts[0].trace[14] = T.clock(2); })],
  S10: [CRASH, edit(CRASH, (h) => { h.attempts[1].trace[4] = T.draw(8); })],
  // Closing issues a durable sleep instead of refusing it.
  S11: [CLOSING, edit(CLOSING, (h) => {
    const a = h.attempts[0];
    a.journalOut.splice(5, 0, { ...C('sleep', 's9', { ms: 1 }), idx: 5 });
    a.journalOut[6].idx = 6;
    a.trace.push(T.issue(5));
    a.end.at += 1;
  })],
  // The cancellation is delivered before the earlier-journaled result r1.
  S12: [ORDER, edit(ORDER, (h) => {
    const a = h.attempts[0];
    a.journalOut = J(S(), N(0, ok(0)), C('run', 'r1'), N(2, ok('v')), X(), S(),
      N(5, ok(1)), S(), N(7, ok(1)), O('cancelled'));
    a.trace = [...first(), T.issue(2), T.consume(3), T.turn('journal', 4), T.issue(5),
      T.consume(4), T.consume(6), T.sample(5, 1), T.interrupt('f0', 'cancel'),
      ...jturn(3, 7, 8, 1), T.deliver('r1', ok('v')), T.exit('cancelled')];
    a.end.at = a.trace.length - 1;
  })],
  // The second cancel signal interrupts the root again.
  S13: [TWO_CANCEL, edit(TWO_CANCEL, (h) => {
    h.attempts[0].trace.splice(20, 0, T.interrupt('f0', 'cancel'));
    h.attempts[0].end.at += 1;
  })],
  // The finalizer's start is refused as if closing had begun.
  S14a: [CANCEL, edit(CANCEL, (h) => {
    const a = h.attempts[0];
    a.journalOut = J(...CANCEL_HEAD_J.slice(0, 6), O('defect'));
    a.trace = [...CANCEL_HEAD_T.slice(0, 11), T.violation('refusedAtClosing'), T.exit('defect')];
    a.end.at = a.trace.length - 1;
    h.outcome = { kind: 'defect' };
    h.children = [];
  })],
  // The compensation key counts the send itself: n = 4, not 3.
  S14b: [CANCEL, edit(CANCEL, (h) => {
    const j = h.attempts[0].journalOut;
    j[6].cmd.key = 'inv-1:4';
    j[8].cmd.target = 'inv-1:4';
    h.children[0].key = 'inv-1:4';
  })],
  // The second cancel signal makes the executor cancel the compensation child.
  S14d: [TWO_CANCEL, edit(TWO_CANCEL, (h) => {
    const a = h.attempts[0];
    const out = a.journalOut.pop();
    a.journalOut.push({ ...CC(6, 'executor'), idx: 15 }, { ...out, idx: 16 });
    a.trace.splice(17, 0, T.issue(15));
    a.end.at += 1;
  })],
  // Closing writes output without cancelling the interrupted fiber's call.
  S15: [CLOSING, edit(CLOSING, (h) => {
    const a = h.attempts[0];
    a.journalOut = J(S(), N(0, ok(0)), C('call', 'c1'), N(2, { invocationId: 'k1' }),
      O('success'));
    a.trace.pop();
    a.end.at -= 1;
    h.children[0].cancelled = false;
  })],
  // Output is written before the retained run's result is journaled.
  S16a: [RETAINED, edit(RETAINED, (h) => {
    const a = h.attempts[0];
    a.journalOut = a.journalOut.slice(0, 7).concat([{ ...O('success'), idx: 7 }]);
    a.trace = a.trace.slice(0, 16);
    a.end.at = 15;
  })],
  // While frozen, the executor consumes a result and runs a turn for it.
  S16b: [FREEZE, edit(FREEZE, (h) => {
    const a = h.attempts[0];
    a.journalOut = CRASH_J1.slice(0, 4);
    a.trace.push(T.consume(3), T.turn('journal'));
    a.end.at = 7;
  })],
  // A closure executing when the attempt suspends.
  S16c: [SUSP, hist(RUN.program, [att({ journalOut: J(S(), N(0, ok(0)), C('run', 'r1')),
    trace: [...first(), T.issue(2)], effects: [eff('r1', null)],
    end: { kind: 'suspended', at: 4 } })])],
  // The run lost at the Ended cut is not executed again.
  S16d: [ENDED, edit(ENDED, (h) => { h.attempts[1].effects = []; })],
  // The run lost at the crash is not executed again.
  S16e: [CRASH, edit(CRASH, (h) => { h.attempts[1].effects = []; })],
  // An attempt follows a kill.
  S16f: [KILLED, edit(KILLED, (h) => {
    h.attempts.push({ ...structuredClone(CRASH.attempts[1]),
      journalIn: h.attempts[0].journalOut });
  })],
  // The retained run's result reaches the fiber that lost the race.
  S17: [RETAINED, edit(RETAINED, (h) => {
    h.attempts[0].trace.push(T.deliver('r1', ok('late')));
    h.attempts[0].end.at += 1;
  })],
  // A run that maps the abort to an error of its own is journaled as an abort.
  S18: [DEADLINE, edit(DEADLINE, (h) => {
    h.program.fibers[0].body[0].behaviour = 'mapAbort';
    h.attempts[0].effects = [eff('r1', 'retryable')];
  })],
  // The deadline abort precedes the consumption of the deadline's completion.
  S19: [DEADLINE, edit(DEADLINE, (h) => {
    const t = h.attempts[0].trace;
    [t[6], t[7]] = [t[7], t[6]];
  })],
  // On replay the closure is entered although the journal holds its deadline.
  S20: [REABORT, edit(REABORT, (h) => {
    h.attempts[1].effects = [eff('r1', 'aborted', { attempt: 1 })];
  })],
  // A child's 409 is reported as the parent's cancellation.
  S21: [CALL409, edit(CALL409, (h) => {
    h.attempts[0].journalOut[7].outcome.kind = 'cancelled';
    h.outcome = { kind: 'cancelled' };
  })],
  // An Ended cut leaves an executing run unaborted.
  S22: [ENDED, edit(ENDED, (h) => {
    const a = h.attempts[0];
    a.trace = a.trace.filter((e) => e.t !== 'abort');
    a.effects = [eff('r1', null)];
  })],
  // Closing writes output without interrupting the live forked fiber.
  S23: [CLOSING, edit(CLOSING, (h) => {
    const a = h.attempts[0];
    a.trace.splice(6, 2);
    a.end.at -= 2;
  })],
  // The first warning names a run whose result was already consumed.
  S25: [RETAINED, edit(RETAINED, (h) => {
    const t = h.attempts[0].trace;
    t.splice(16, 2);
    t.push(T.warn(1, ['r1'], 3));
  })],
  // The second warning is emitted twice for the same run.
  S26: [RETAINED, edit(RETAINED, (h) => {
    h.attempts[0].trace.splice(17, 0, T.warn(2, ['r1'], 10));
    h.attempts[0].end.at += 1;
  })],
};

// Extra counterexamples beyond one per predicate.
const EXTRA = [
  // A journal turn applies two samples.
  ['S8.P8', edit(RUN, (h) => {
    const t = h.attempts[0].trace;
    t.splice(10, 0, T.sample(0, 1));
    h.attempts[0].end.at += 1;
  })],
  // A call issued after the cancel signal was consumed stays a plain call.
  ['S13', edit(CANCEL, (h) => { h.attempts[0].journalOut[6].cmd.c = 'call'; })],
  // The closure is entered with its signal already aborted.
  ['S20', edit(DEADLINE, (h) => {
    h.attempts[0].effects = [eff('r1', 'aborted', { abortedAtEntry: true })];
  })],
  // A retried attempt decides a final outcome.
  ['S21', edit(FREEZE, (h) => { h.attempts.pop(); })],
  // A crashed attempt keeps producing events.
  ['S22', edit(CRASH, (h) => { h.attempts[0].end.at = 3; })],
  // The executor cancels a call that had already completed.
  ['S15', edit(CALL409, (h) => {
    const a = h.attempts[0];
    a.journalOut.splice(7, 0, { ...CC(2, 'executor'), idx: 7 });
    a.journalOut[8].idx = 8;
    a.trace.push(T.issue(7));
  })],
  // An entry consumed past a run result the race skipped.
  ['S4', edit(TWO_RUNS, (h) => {
    const t = h.attempts[0].trace;
    t.splice(9, 1);
    t.splice(14, 0, T.consume(5));
  })],
  // A retryable closure failure ends in output.
  ['S16b', edit(RUN, (h) => { h.attempts[0].effects = [eff('r1', 'retryable')]; })],
];

// Counterexamples for the revised format.
EXTRA.push(
  // The dropped loser's result gets a turn and a sample.
  ['S12', edit(DROP, (h) => {
    const a = h.attempts[0];
    a.journalOut = J(...a.journalOut.slice(0, 8), S(), N(8, ok(0)), O('success'));
    a.trace.splice(15, 0, ...jturn(6, 8, 9, 0));
    a.end.at = a.trace.length - 1;
  })],
  // Turns take the two buffered results out of queue order.
  ['S7', edit(TWO_RUNS, (h) => {
    const t = h.attempts[0].trace;
    t[7] = T.turn('journal', 5);
    t[12] = T.deliver('r2', ok('b'));
    t[13] = T.turn('journal', 4);
    t[17] = T.deliver('r1', ok('a'));
  })],
  // A journal turn that names no cause.
  ['S7', edit(RUN, (h) => { h.attempts[0].trace[6] = T.turn('journal'); })],
  // A closure refused while its signal is live: not a held closure.
  ['S20', edit(HELD, (h) => {
    h.attempts[0].effects = [eff('r1', null, { entered: false })];
  })],
  // The first cancel's turn ran past its sample (the root read the clock)
  // without interrupting the root, then the attempt was killed.
  ['S13', edit(CUT_AFTER_SAMPLE, (h) => {
    h.attempts[0].trace.push(T.clock(1));
    h.attempts[0].end.at += 1;
  })],
  // The retried run neither executes again nor is refused with its abort.
  ['S16b', edit(FREEZE, (h) => { h.attempts[1].effects = []; })],
  // A retryable root exit writes Output.
  ['S21', edit(RETRY_ROOT, (h) => {
    h.attempts[0].journalOut.push({ ...O('success'), idx: 2 });
  })],
  // The replay issued a command different from the journal's.
  ['S2', edit(CRASH, (h) => { h.attempts[1].end.detail = 'mismatch'; })],
  // The race consumes the released loser's result.
  ['S4', edit(RACE_SLEEP, (h) => {
    const a = h.attempts[0];
    a.journalOut = J(...a.journalOut.slice(0, 7), N(3, ok()), O('success'));
    a.trace.splice(14, 0, T.consume(7));
    a.end.at += 1;
  })],
);

// Counterexamples for exit releases.
const EXIT_OUTPUT_EARLY = edit(EXIT_RUN, (h) => {
  const a = h.attempts[0];
  a.journalOut = J(S(), N(0, ok(0)), C('run', 'r1'), O('success'));
  a.trace.pop();
  a.end.at -= 1;
  a.effects = [];
});
EXTRA.push(
  // The executor does not cancel the unawaited call at exit.
  ['S15', edit(EXIT_CALL, (h) => {
    const a = h.attempts[0];
    a.journalOut = J(S(), N(0, ok(0)), C('call', 'c1'), N(2, { invocationId: 'k1' }),
      O('success'));
    a.trace.pop();
    a.end.at -= 1;
    h.children[0].cancelled = false;
  })],
  // The unawaited run is not aborted at exit.
  ['S18', edit(EXIT_RUN, (h) => {
    const a = h.attempts[0];
    a.trace.splice(7, 1);
    a.end.at -= 1;
  })],
  // Output written before the retained run's result was consumed.
  ['S17', EXIT_OUTPUT_EARLY],
  ['S23', EXIT_OUTPUT_EARLY],
  // On replay the closure is entered although the journal rebuilds the
  // exit abort.
  ['S20', edit(EXIT_REABORT, (h) => {
    h.attempts[1].effects = [eff('r1', 'ok', { attempt: 1 })];
  })],
);

EXTRA.push(['S20', edit(CLOSE_REABORT, (h) => {
  // The replay enters the closure that closing's interruption aborted.
  h.attempts[1].effects = [eff('r1', 'ok', { attempt: 1 })];
})]);

EXTRA.push(
  ['S20', GATE_BAD],             // C24 entry gate
  ['S20', SAMPLE_WAIT],          // M7: a sample waited at the gate
  ['S20', SAMPLE_HELD],          // M7: output with a sample's wrapper held
  ['S16b', RETRY_NO_FREEZE],     // C18: no freeze after a retryable settle
  ['S16b', RETRY_ENTERS],        // C18: a closure entered after it
  ['S16b', RETRY_BAD_ORDER],     // M2: success proposed after the failure
  ['S16b', RETRY_DELIVERS],      // M8: a delivery after the retryable settle
  ['S16b', RETRY_EARLY_FREEZE],  // M8: freeze before the retryable settle
);

EXTRA.push(
  ['S1', edit(LIFE_REPLAY, (h) => { h.attempts[1].trace[4] = T.draw(8); })],
  ['S16b', RETRY_LATE_BAD],      // M2: a success settled in the freeze, proposed late
  ['S20', SAMPLE_KILLED_HELD],   // M7: a kill with a sample's wrapper held
  ['S16b', DONE_HELD],           // M8: settlement held past the next turn's command
  ['S16b', TWO_RETRY_BAD],       // M8: freeze on a later retryable completion
);

EXTRA.push(
  ['S16b', DONE_NEXT_TURN],   // M8: a closing turn between a done and its settle
  ['S13', RECANCEL_BAD],      // the second signal makes the SDK cancel c1 again
);

// Accepted by one predicate: a retried run refused at the gate on the next
// attempt, with its terminal abort journaled (S16(d), "unless S20 applies").
const FREEZE_REFUSED = edit(FREEZE, (h) => {
  const a = h.attempts[1];
  a.journalOut[3].value = { terminal: 'aborted' };
  a.effects = [eff('r1', 'aborted', { attempt: 1, entered: false, abortedAtEntry: true })];
});
const ACCEPT_ONLY = [['S16b', FREEZE_REFUSED], ['S16e', REABORT_NO_EFFECT]];

// --------------------------------------------------- pair predicates

const PAIR_CASES = {
  S1: [[CRASH, LIVE], [CRASH, edit(LIVE, (h) => { h.attempts[0].trace[4] = T.draw(8); })]],
  S2: [[CRASH, LIVE], [LIVE, edit(LIVE, (h) => {
    h.attempts[0].journalOut[2].cmd = { c: 'sleep', op: 'r1', ms: 1 };
  })]],
  S3: [[CRASH, LIVE], [LIVE, edit(LIVE, (h) => {
    h.attempts[0].trace[4] = T.violation('other');
  })]],
  S10: [[CRASH, LIVE], [LIVE, edit(LIVE, (h) => { h.attempts[0].trace[4] = T.draw(9); })]],
};

const LATE_CANCEL = edit(RUN, (h) => {
  const a = h.attempts[0];
  a.journalOut.splice(6, 0, { ...X(), idx: 6 });
  a.journalOut[7].idx = 7;
  a.trace.push(T.consume(6));
  a.end.at += 1;
});

// Fills the contents HISTORY.md puts on `issue` (cmd) and `consume` (entry)
// from the journals, as the model records them. A command lost to a crash is
// looked up in a later attempt's journal at the same index.
const withContents = (h) => edit(h, (c) => c.attempts.forEach((a, k) => {
  const find = (idx) => [a, ...c.attempts.slice(k + 1)]
    .map((x) => x.journalOut.find((e) => e.idx === idx)).find(Boolean);
  a.trace.forEach((e) => {
    const entry = (e.t === 'issue' || e.t === 'consume') ? find(e.t === 'issue' ? e.cmdIdx : e.entryIdx) : null;
    if (e.t === 'issue' && entry?.e === 'cmd') e.cmd = entry.cmd;
    if (e.t === 'consume' && entry) e.entry = entry;
  });
}));

/** Every hand-built history in this file, by name, for monitors.test.mjs. */
export const HISTORIES_RAW = [
  ...Object.entries(VALID),
  ...Object.entries(CASES).flatMap(([id, [good, bad]]) => [[`${id}:good`, good], [`${id}:bad`, bad]]),
  ...EXTRA.map(([id, bad], k) => [`extra${k}:${id}`, bad]),
  ...ACCEPT_ONLY.map(([id, good], k) => [`accept${k}:${id}`, good]),
  ...Object.entries(PAIR_CASES).flatMap(([id, pairs]) =>
    pairs.flat().map((h, k) => [`pair:${id}:${k}`, h])),
  ['LATE_CANCEL', LATE_CANCEL],
];
export const HISTORIES = HISTORIES_RAW.map(([name, h]) => [name, withContents(h)]);

// --------------------------------------------------------- runner

const main = () => {

  let failures = 0;
  const report = (ok, label, extra = '') => {
    if (!ok) failures += 1;
    console.log(`${ok ? 'ok  ' : 'FAIL'} ${label}${extra}`);
  };
  const byId = new Map(predicates.map((p) => [p.id, p]));
  const pairById = new Map(pairPredicates.map((p) => [p.id, p]));

  const runCheck = (pred, h) => {
    try { return { result: pred.check(h) }; } catch (error) { return { error }; }
  };

  // Every valid history, as written and with issue and consume contents.
  Object.entries(VALID).flatMap(([name, h]) => [[name, h], [`${name}+contents`, withContents(h)]])
    .forEach(([name, h]) => predicates.forEach((p) => {
    const { result, error } = runCheck(p, h);
    if (error || result) {
      report(false, `${p.id} accepts valid ${name}`,
        `: ${error ? error.stack : JSON.stringify(result)}`);
    }
  }));
  report(failures === 0, `all ${predicates.length} predicates accept all ${Object.keys(VALID).length} valid histories`);

  const expectBoth = (pred, good, bad, label) => {
    const g = runCheck(pred, good);
    report(!g.error && g.result === null, `${label} accepts`,
      g.error ? `: ${g.error.stack}` : g.result ? `: ${JSON.stringify(g.result)}` : '');
    const b = runCheck(pred, bad);
    report(!b.error && b.result !== null, `${label} rejects`,
      b.error ? `: ${b.error.stack}` : b.result ? `: ${b.result.msg}` : ': accepted');
  };

  predicates.forEach((p) => {
    const pair = CASES[p.id];
    if (!pair) { report(false, `${p.id} has no test case`); return; }
    expectBoth(p, pair[0], pair[1], p.id);
  });
  ACCEPT_ONLY.forEach(([id, good]) => {
    const g = runCheck(byId.get(id), good);
    report(!g.error && g.result === null, `${id} accepts extra case`,
      g.error ? `: ${g.error.stack}` : g.result ? `: ${JSON.stringify(g.result)}` : '');
  });
  EXTRA.forEach(([id, bad]) => {
    const b = runCheck(byId.get(id), bad);
    report(!b.error && b.result !== null, `${id} rejects extra case`,
      b.error ? `: ${b.error.stack}` : b.result ? `: ${b.result.msg}` : ': accepted');
  });

  pairPredicates.forEach((p) => {
    const cases = PAIR_CASES[p.id];
    if (!cases) { report(false, `pair ${p.id} has no test case`); return; }
    const [[a1, b1], [a2, b2]] = cases;
    const g = p.check(a1, b1);
    report(g === null, `pair ${p.id} accepts`, g ? `: ${JSON.stringify(g)}` : '');
    const b = p.check(a2, b2);
    report(b !== null, `pair ${p.id} rejects`, b ? `: ${b.msg}` : ': accepted');
  });
  report(pairById.get('S1').check(RUN, CRASH) === null, 'pair predicates skip different programs');

  const tags = (h) => [...boundaries(h)];
  const expectTags = (name, h, want) => {
    const got = tags(h);
    const missing = want.filter((t) => !got.includes(t));
    report(missing.length === 0, `boundaries ${name}`, missing.length ? `: missing ${missing}` : '');
  };
  expectTags('CRASH', CRASH, ['end:crashed', 'end:output', 'replay']);
  expectTags('TWO_CANCEL', TWO_CANCEL, ['cancel:unwinding', 'cancel:twice', 'compensation:send']);
  expectTags('ORDER', ORDER, ['cancel:duringSample']);
  expectTags('RETAINED', RETAINED, ['run:retained', 'race:loser', 'closing:wait']);
  expectTags('UNSTARTED', UNSTARTED, ['run:unstartedRetained']);
  expectTags('SLEEPS', SLEEPS, ['sleep:overlap']);
  expectTags('CHAIN', CHAIN, ['sleep:chain']);
  expectTags('FREEZE', FREEZE, ['freeze', 'end:retry']);
  expectTags('DEADLINE', DEADLINE, ['deadline:fired']);
  expectTags('ENDED', ENDED, ['end:ended']);
  expectTags('KILLED', KILLED, ['end:killed']);
  expectTags('SUSP', SUSP, ['end:suspended']);
  expectTags('UNINT', UNINT, ['uninterruptible']);
  expectTags('DROP', DROP, ['race:loser']);

  expectTags('LATE_CANCEL', LATE_CANCEL, ['cancel:afterRootExit']);
  report(predicates.every((p) => p.check(LATE_CANCEL) === null), 'a cancel after the root exit is absorbed');

  console.log(failures ? `\n${failures} failure(s)` : '\nall passed');
  process.exit(failures ? 1 : 0);
};

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) main();
