// Self-test for monitors.mjs. Run: node monitors.test.mjs
// Feeds every hand-built history of predicates.test.mjs, as a stream built
// exactly as HISTORY.md's last section defines it, to every monitor, and
// checks that:
// - each monitor's verdict is null exactly when its predicate's is;
// - step never mutates the state it is given;
// - every state is plain JSON (objects, arrays, strings, finite numbers,
//   booleans, null), so states compare by serialization.
// Prints, per monitor, the largest serialized state seen. Exits non-zero on
// any failure.

import { monitors } from './monitors.mjs';
import { predicates } from './predicates.mjs';
import { HISTORIES } from './predicates.test.mjs';

const streamOf = (history) => [
  { s: 'program', program: history.program },
  ...history.attempts.flatMap((att) => [
    { s: 'attemptStart', n: att.n, journalIn: att.journalIn },
    ...att.trace.map((event) => ({ s: 'event', event })),
    { s: 'attemptEnd', end: att.end, journalOut: att.journalOut, effects: att.effects },
  ]),
  { s: 'invocationEnd', outcome: history.outcome, children: history.children },
];

const isPlain = (v) => {
  if (v === null || typeof v === 'string' || typeof v === 'boolean') return true;
  if (typeof v === 'number') return Number.isFinite(v);
  if (Array.isArray(v)) return v.every(isPlain);
  if (typeof v === 'object' && Object.getPrototypeOf(v) === Object.prototype) {
    return Object.values(v).every((x) => x !== undefined && isPlain(x));
  }
  return false;
};

let failures = 0;
const report = (ok, label, extra = '') => {
  if (!ok) failures += 1;
  if (!ok) console.log(`FAIL ${label}${extra}`);
};

const byId = new Map(predicates.map((p) => [p.id, p]));
report(monitors.length === predicates.length
  && monitors.every((m) => byId.has(m.id)), 'one monitor per predicate, same ids');

const largest = new Map(monitors.map((m) => [m.id, 0]));
let compared = 0;

const runMonitor = (m, stream, label) => {
  let M = m.init();
  for (const item of stream) {
    const before = JSON.stringify(M);
    const next = m.step(M, item);
    if (JSON.stringify(M) !== before) report(false, `${m.id} mutated its state on ${label}`);
    if (!isPlain(next)) report(false, `${m.id} state is not plain JSON on ${label}`);
    largest.set(m.id, Math.max(largest.get(m.id), JSON.stringify(next).length));
    M = next;
  }
  return m.verdict(M);
};

HISTORIES.forEach(([name, h]) => {
  const stream = streamOf(h);
  monitors.forEach((m) => {
    const want = byId.get(m.id).check(h);
    let got;
    try { got = runMonitor(m, stream, name); } catch (error) {
      report(false, `${m.id} threw on ${name}`, `: ${error.stack}`);
      return;
    }
    compared += 1;
    report((want === null) === (got === null), `${m.id} agrees with its predicate on ${name}`,
      `: predicate ${JSON.stringify(want)}, monitor ${JSON.stringify(got)}`);
  });
});

// Gate integrity: the agreement check must be able to fail. A monitor that
// never sees trace events must disagree with its predicate somewhere.
const blind = (m) => ({ ...m, step: (M, item) => (item.s === 'event' ? M : m.step(M, item)) });
['S7', 'S8.P2', 'S12'].forEach((id) => {
  const m = blind(monitors.find((x) => x.id === id));
  const disagree = HISTORIES.filter(([, h]) =>
    (byId.get(id).check(h) === null) !== (runMonitor(m, streamOf(h), 'blind') === null));
  report(disagree.length > 0, `a blind ${id} monitor is caught`);
  console.log(`blind ${id} monitor disagrees on ${disagree.length} histories`);
});

const rejected = HISTORIES.reduce((n, [, h]) =>
  n + predicates.filter((p) => p.check(h) !== null).length, 0);
console.log(`${HISTORIES.length} histories x ${monitors.length} monitors: ${compared} verdicts compared, ${rejected} of them rejections`);
console.log('largest serialized state per monitor (bytes):');
[...largest].forEach(([id, size]) => console.log(`  ${id.padEnd(8)} ${size}`));
console.log(failures ? `\n${failures} failure(s)` : '\nall passed');
process.exit(failures ? 1 : 0);
