// Online monitors, one per predicate in predicates.mjs (same ids). Each is
// { id, init(), step(M, item), verdict(M) } over the event stream of
// HISTORY.md's last section, with M plain JSON; step never mutates its M.
//
// These are written from the statements, independently of predicates.mjs:
// they import nothing from it. The predicates are the reference; the test
// (monitors.test.mjs) checks that each monitor's verdict is null exactly
// when its predicate's is, on every hand-built history.
//
// State discipline. A monitor keeps no event list. Per attempt it keeps a
// small base (event count, the positions of the root's exit, the first
// violation and the freeze, the commands issued so far as { c, op, fiber },
// and the open turn) and what its own claim needs, listed at each monitor.
// Positions are kept only where the claim depends on the attempt's cut
// (end.at), which the stream reveals only at attemptEnd: such a failure is
// held as "pending at position p" and confirmed if p <= end.at. Across
// attempts a monitor keeps only its claim's summary.

const ABORTED = 'aborted';
const isId = (v) => !!v && typeof v === 'object' && 'invocationId' in v;
const same = (a, b) => JSON.stringify(sortKeys(a)) === JSON.stringify(sortKeys(b));
const sortKeys = (v) => {
  if (Array.isArray(v)) return v.map(sortKeys);
  if (v && typeof v === 'object') {
    return Object.fromEntries(Object.keys(v).sort().map((k) => [k, sortKeys(v[k])]));
  }
  return v;
};
const fail = (msg, detail = {}) => ({ msg, detail: JSON.parse(JSON.stringify(detail)) });
// Drops keys whose value is undefined, so state stays plain JSON.
const def = (o) => Object.fromEntries(Object.entries(o).filter(([, v]) => v !== undefined));
const isSampleOp = (op) => typeof op === 'string' && op.startsWith('sample:');

// ------------------------------------------------------------ program

// { root, daemon: { fiber: bool }, ops: { op: { fiber, s, ms, deadline, prot } } }
const indexProgram = (program) => {
  const ops = {};
  const visit = (fiber, prot) => (st) => {
    if (['run', 'sleep', 'call'].includes(st.s)) {
      ops[st.op] = { fiber, s: st.s, prot,
        ...(st.ms !== undefined ? { ms: st.ms } : {}),
        ...(st.deadline !== undefined ? { deadline: st.deadline } : {}) };
    }
    if (st.s === 'uninterruptible') st.body.forEach(visit(fiber, true));
    if (st.s === 'ensuring') {
      st.body.forEach(visit(fiber, prot));
      st.finalizer.forEach(visit(fiber, true));
    }
  };
  program.fibers.forEach((f) => f.body.forEach(visit(f.id, false)));
  return { root: program.fibers[0]?.id ?? 'f0',
    daemon: Object.fromEntries(program.fibers.map((f) => [f.id, !!f.daemon])), ops };
};

// --------------------------------------------------------- the frame

// The base every monitor keeps for the open attempt.
const baseAttempt = (item) => ({
  n: item.n, pos: 0, rootExit: null, viol: null, freeze: null,
  cmd: {}, jin: Object.fromEntries(item.journalIn.filter((e) => e.e === 'cmd')
    .map((e) => [e.idx, def({ c: e.cmd.c, op: e.cmd.op })])),
  seg: null, nSeg: 0, pend: null, hit: null,
});

const closing = (a) => Math.min(a.rootExit ?? Infinity, a.viol ?? Infinity);
// A failure that holds if `pos` is within the cut; an infinite position
// can never be within it.
const pend = (a, pos, f) => {
  if (Number.isFinite(pos) && (!a.pend || pos < a.pend.pos)) a.pend = { pos, f };
};
const hit = (a, f) => { if (!a.hit) a.hit = f; };

const cmdOf = (a, idx) => a.cmd[idx] ?? a.jin[idx] ?? null;
const classify = (a, entry) => {
  if (!entry) return { k: 'missing' };
  if (entry.e === 'cancel') return { k: 'cancel' };
  if (entry.e !== 'notif') return { k: entry.e };
  const cmd = cmdOf(a, entry.of);
  if (!cmd) return { k: 'orphan' };
  if (isId(entry.value)) return { k: 'id', c: cmd.c, op: cmd.op };
  if (cmd.c === 'run' && cmd.op === 'sample') return { k: 'sample' };
  if (cmd.c === 'sleep' && cmd.op === 'deadline') return { k: 'deadline' };
  return { k: 'result', c: cmd.c, op: cmd.op };
};

const trackBase = (a, e) => {
  if (e.t === 'rootExit' && a.rootExit === null) a.rootExit = e.pos;
  if (e.t === 'violation' && a.viol === null) a.viol = e.pos;
  if (e.t === 'freeze' && a.freeze === null) a.freeze = e.pos;
  if (e.t === 'issue' && !(e.cmdIdx in a.cmd) && e.cmd) {
    a.cmd[e.cmdIdx] = def({ c: e.cmd.c, op: e.cmd.op, fiber: e.fiber });
  }
};

const journalCmd = (journal, idx) => {
  const e = journal.find((x) => x.idx === idx);
  return e?.e === 'cmd' ? e.cmd : null;
};
const runResult = (journal, op) => {
  const runs = new Set(journal.filter((e) => e.e === 'cmd' && e.cmd.c === 'run'
    && e.cmd.op === op).map((e) => e.idx));
  return journal.find((e) => e.e === 'notif' && runs.has(e.of) && !isId(e.value)) ?? null;
};
const outputIdx = (journal) => journal.find((e) => e.e === 'output')?.idx ?? Infinity;

// Wraps a claim into a monitor. A claim is { x0(), start(a, item, P, x),
// event(a, e, P, x), turnEnd(a, seg, P, x), end(a, item, P, x),
// final(x, item, P) }; every part is optional and mutates the clones it is
// given. `end` sees a.cut.
// A fast copy of plain JSON.
const copy = (v) => {
  if (v === null || typeof v !== 'object') return v;
  if (Array.isArray(v)) {
    const out = new Array(v.length);
    for (let i = 0; i < v.length; i += 1) out[i] = copy(v[i]);
    return out;
  }
  const out = {};
  for (const k in v) out[k] = copy(v[k]);
  return out;
};

// Copy-on-write. A step never mutates the state it is given: it shallow-
// copies the state and copies only what the step writes in place.
// - The program index is written once, then shared.
// - The cross-attempt summary x is written only by start, end and final
//   hooks, so a trace event shares it; a boundary item copies it.
// - On a trace event the open attempt is shallow-copied (its scalar fields
//   are then the step's own), and only the fields written in place are
//   copied: the base's commands and open turn when the event writes them,
//   and the fields the claim lists in `mut` for the event's type. Every other field of the attempt is only ever replaced,
//   never written in place, so sharing it is safe. monitors.test.mjs checks
//   on every history that no step changes its input.
// - On a boundary item: attemptStart builds a fresh attempt, and its start
//   hooks only read x; attemptEnd's end and turnEnd hooks only read the
//   attempt and replace its scalar fields, and the attempt is dropped after
//   them, so a shallow copy suffices; x is copied whole there and at
//   invocationEnd, where hooks append to it.
// Copies v to the given depth and shares what lies deeper.
const copyTo = (v, depth) => {
  if (depth === 0 || v === null || typeof v !== 'object') return v;
  if (Array.isArray(v)) return depth === 1 ? v.slice() : v.map((x) => copyTo(x, depth - 1));
  if (depth === 1) return { ...v };
  const out = {};
  for (const k of Object.keys(v)) out[k] = copyTo(v[k], depth - 1);
  return out;
};

// A field written in place is listed as "name" (its own entries are set or
// appended, never changed) or "name:d" (parts d - 1 levels below it are
// changed in place): it is copied to that depth.
const parseFields = (fields) => fields.map((f) => {
  const [k, d] = f.split(':');
  return [k, d ? Number(d) : 1];
});

const copyFields = (out, a, fields) => {
  for (const [k, d] of fields) if (k in a) out[k] = copyTo(a[k], d);
  return out;
};

// The base writes its command map only on an issue, and its open turn only
// on a sample, issue, delivery or interruption, or on the event right after
// the turn's first sample. The open turn's arrays are replaced, never
// appended to in place, so a one-level copy of the turn suffices.
const SEG_WRITERS = new Set(['sample', 'issue', 'deliver', 'interrupt']);
const copyBase = (out, a, t) => {
  if (t === 'issue') out.cmd = { ...a.cmd };
  const seg = a.seg;
  if (seg && (SEG_WRITERS.has(t) || (seg.samples.length > 0 && seg.afterSample === null))) {
    out.seg = { ...seg };
  }
};

const stepEvent = (claim, M0, item) => {
  const t = item.event.t;
  const a = { ...M0.a };
  copyBase(a, M0.a, t);
  const mine = claim.mut0[t];
  if (mine) copyFields(a, M0.a, mine);
  const e = { ...item.event, pos: a.pos };
  a.pos += 1;
  if (e.t === 'turn') openTurn(claim, a, e, M0.P, M0.x);
  trackBase(a, e);
  if (a.seg) noteTurn(a.seg, e);
  if (claim.event) claim.event(a, e, M0.P, M0.x);
  const verdict = a.hit && !claim.deferHits ? tag(a.hit, a.n) : null;
  return { P: M0.P, a, x: M0.x, verdict };
};

const stepBoundary = (claim, M0, item) => {
  const writesX = item.s === 'attemptEnd' || item.s === 'invocationEnd';
  const M = { P: M0.P, a: M0.a && { ...M0.a }, x: writesX ? copy(M0.x) : M0.x, verdict: null };
  if (item.s === 'program') M.P = indexProgram(item.program);
  if (item.s === 'attemptStart') {
    M.a = { ...baseAttempt(item), ...(claim.fresh ? claim.fresh(item) : {}) };
    if (claim.start) claim.start(M.a, item, M.P, M.x);
  }
  if (item.s === 'attemptEnd') {
    const a = M.a;
    a.cut = item.end.at;
    a.endKind = item.end.kind;
    if (a.seg && claim.turnEnd) claim.turnEnd(a, a.seg, M.P, M.x, Infinity);
    const voided = claim.voids ? claim.voids(a) : false;
    const f = voided ? null : a.hit ?? (a.pend && a.pend.pos <= a.cut ? a.pend.f : null)
      ?? (claim.end ? claim.end(a, item, M.P, M.x) : null);
    if (f) M.verdict = tag(f, a.n);
    M.a = null;
  }
  if (item.s === 'invocationEnd' && claim.final) {
    M.verdict = claim.final(M.x, item, M.P) ?? null;
  }
  return M;
};

// Wraps a claim into a monitor. A claim is { x0(), fresh(item),
// start(a, item, P, x), event(a, e, P, x), turnEnd(a, seg, P, x, nextPos),
// end(a, item, P, x), final(x, item, P) }; every part is optional and may
// write only the copies it is given (a, and x outside event hooks). `end`
// sees a.cut.
const monitor = (id, claim0) => {
  const mut0 = Object.fromEntries(Object.entries(claim0.mut ?? {}).map(([t, f]) => [t, parseFields(f)]));
  const claim = { ...claim0, mut0 };
  return {
  id,
  init: () => ({ P: null, a: null, x: claim.x0 ? claim.x0() : {}, verdict: null }),
  step: (M0, item) => {
    if (M0.verdict) return M0;
    return item.s === 'event' ? stepEvent(claim, M0, item) : stepBoundary(claim, M0, item);
  },
  verdict: (M) => M.verdict,
  };
};

const tag = (f, n) => ({ msg: f.msg, detail: { attempt: n, ...f.detail } });

// The open turn's summary: where it started, its cause, its sample, the
// first event after the sample, its deliveries and its issues.
const openTurn = (claim, a, e, P, x) => {
  if (a.seg && claim.turnEnd) claim.turnEnd(a, a.seg, P, x, e.pos);
  a.nSeg += 1;
  a.seg = { start: e.pos, cause: e.cause, entryIdx: e.entryIdx ?? null, k: a.nSeg,
    samples: [], afterSample: null, dels: [], issues: [], acts: [] };
};

const noteTurn = (seg, e) => {
  const firstSample = seg.samples[0];
  if (firstSample !== undefined && seg.afterSample === null && e.pos === firstSample.pos + 1) {
    seg.afterSample = { pos: e.pos, t: e.t };
  }
  if (e.t === 'sample') seg.samples = [...seg.samples, { pos: e.pos, cmdIdx: e.cmdIdx }];
  if (e.t === 'issue') seg.issues = [...seg.issues, def({ pos: e.pos, idx: e.cmdIdx, c: e.cmd?.c, op: e.cmd?.op })];
  if (e.t === 'deliver') seg.dels = [...seg.dels, { pos: e.pos, op: e.op, value: e.value }];
  if (e.t === 'deliver' || e.t === 'interrupt') seg.acts = [...seg.acts, { pos: e.pos, t: e.t, cause: e.cause ?? null }];
};

// A turn is complete once it ran past its sample inside the attempt: the
// next turn started within the cut, or the event right after its sample
// (other than a freeze or a warning) is within the cut. Returns the
// earliest position whose being within the cut makes it complete.
const completeFrom = (seg, nextPos) => {
  const after = seg.afterSample && !['freeze', 'warn'].includes(seg.afterSample.t)
    ? seg.afterSample.pos : Infinity;
  return Math.min(nextPos, after);
};

// =====================================================================
// S1, S3, S10: comparisons across attempts.
// Kept per attempt: its inputs (consumed entries, in order) and what the
// claim compares of its observable events (issues, deliveries, interrupts,
// clock reads, draws, violations and the root's exit), each tagged with the
// number of inputs seen before it, up to its cut or freeze.
// S1 keeps every observable event and the journaled command of each issue;
// S3 keeps the count of observable events per input count and the
// violations; S10 keeps the draws. The comparison is the predicate's
// "same inputs up to a point" (#37 X1).

const OBSERVABLE = new Set(['issue', 'deliver', 'interrupt', 'clock', 'draw', 'violation', 'rootExit']);

const observedForm = (e) => {
  if (e.t === 'issue') return { t: 'issue', fiber: e.fiber, cmdIdx: e.cmdIdx };
  const { pos, ...rest } = e;
  return rest;
};

const projectionClaim = (keep, compare) => ({
  mut: { consume: ['inputs'], ...Object.fromEntries([...OBSERVABLE].map((t) => [t, ['kept']])) },
  x0: () => ({ past: [] }),
  fresh: () => ({ inputs: [], kept: [] }),
  event: (a, e) => {
    if (e.t === 'consume') a.inputs.push({ pos: e.pos, entry: e.entry ?? { missing: e.entryIdx } });
    if (OBSERVABLE.has(e.t)) {
      const k = keep(e);
      if (k !== undefined) a.kept.push({ pos: e.pos, seen: a.inputs.length, k });
    }
  },
  end: (a, item, P, x) => {
    const limit = Math.min(a.cut + 1, a.freeze ?? Infinity);
    const inputs = a.inputs.filter((i) => i.pos < limit).map((i) => i.entry);
    const kept = a.kept.filter((o) => o.pos < limit).map((o) => ({ seen: o.seen, k: o.k }));
    const cmds = {};
    kept.filter((o) => o.k?.t === 'issue').forEach((o) => {
      const c = journalCmd(item.journalOut, o.k.cmdIdx);
      if (c) cmds[o.k.cmdIdx] = c;
    });
    const mine = { n: a.n, inputs, kept, cmds };
    const f = x.past.map((p) => compare(p, mine)).find(Boolean) ?? null;
    x.past.push(mine);
    return f;
  },
});

// How far two attempts must agree: k inputs in common; diverged when both
// went on to a different input.
const agreeUpTo = (A, B) => {
  let k = 0;
  while (k < A.inputs.length && k < B.inputs.length && same(A.inputs[k], B.inputs[k])) k += 1;
  return { k, diverged: k < A.inputs.length && k < B.inputs.length };
};

// S1: every observable event, compared in order.
const S1 = projectionClaim((e) => observedForm(e), (A, B) => {
  const { k, diverged } = agreeUpTo(A, B);
  const a = A.kept.filter((o) => o.seen <= k).map((o) => o.k);
  const b = B.kept.filter((o) => o.seen <= k).map((o) => o.k);
  for (let i = 0; i < Math.min(a.length, b.length); i += 1) {
    if (!same(a[i], b[i])) return fail('traces differ before the common cut', { i, a: a[i], b: b[i] });
    if (a[i].t === 'issue') {
      const [ca, cb] = [A.cmds[a[i].cmdIdx], B.cmds[b[i].cmdIdx]];
      if (ca && cb && !same(ca, cb)) return fail('same inputs, different command', { i });
    }
  }
  return diverged && a.length !== b.length ? fail('traces differ before the common cut') : null;
});

// S3: positions of violations among observable events.
const S3 = projectionClaim((e) => (e.t === 'violation' ? { v: e.kind } : null), (A, B) => {
  const { k } = agreeUpTo(A, B);
  const a = A.kept.filter((o) => o.seen <= k);
  const b = B.kept.filter((o) => o.seen <= k);
  const reach = Math.min(a.length, b.length);
  const at = (l) => l.slice(0, reach).map((o, i) => (o.k ? [i, o.k.v] : null)).filter(Boolean);
  return same(at(a), at(b)) ? null : fail('violations at different positions', { a: at(a), b: at(b) });
});

// S10: each fiber's draws.
const S10 = projectionClaim((e) => (e.t === 'draw' ? { f: e.fiber, v: e.value } : undefined), (A, B) => {
  const { k, diverged } = agreeUpTo(A, B);
  const draws = (P) => {
    const m = {};
    P.kept.filter((o) => o.seen <= k && o.k).forEach((o) => { (m[o.k.f] ??= []).push(o.k.v); });
    return m;
  };
  const [da, db] = [draws(A), draws(B)];
  const prefix = (s, l) => s.length <= l.length && s.every((v, i) => same(v, l[i]));
  const bad = [...new Set([...Object.keys(da), ...Object.keys(db)])].find((f) => {
    const [xa, xb] = [da[f] ?? [], db[f] ?? []];
    return diverged ? !same(xa, xb) : !(prefix(xa, xb) || prefix(xb, xa));
  });
  return bad ? fail('draws differ', { fiber: bad }) : null;
});

// =====================================================================
// S2: commands issued in journal order, by their owners, the same on replay.
// Kept for the open attempt: the issues so far (index, fiber, position).
// Kept across attempts: each attempt's first issuer and command per index.

const S2 = {
  mut: { issue: ['iss'] },
  x0: () => ({ firsts: [] }),
  fresh: () => ({ iss: [] }),
  event: (a, e) => { if (e.t === 'issue') a.iss.push({ pos: e.pos, idx: e.cmdIdx, fiber: e.fiber }); },
  end: (a, item, P, x) => {
    const out = item.journalOut;
    if (item.end.detail === 'mismatch') return fail('replay issued a command different from the journal\'s');
    const byIdx = Object.fromEntries(out.map((e) => [e.idx, e]));
    const ownedOk = a.iss.find((i) => {
      const c = byIdx[i.idx]?.e === 'cmd' ? byIdx[i.idx].cmd : null;
      const owner = P.ops[c?.op]?.fiber;
      return c && ['run', 'sleep', 'call', 'send'].includes(c.c) && owner && i.fiber !== owner;
    });
    const f = prefixOk(a, out) ?? orderOk(a, out, byIdx)
      ?? (ownedOk ? fail('command issued by a fiber that does not own it', ownedOk) : null)
      ?? issuerStable(a, x, byIdx);
    const first = {};
    a.iss.forEach((i) => {
      if (!(i.idx in first)) {
        first[i.idx] = { fiber: i.fiber, cmd: byIdx[i.idx]?.e === 'cmd' ? byIdx[i.idx].cmd : null };
      }
    });
    x.firsts.push(first);
    return f;
  },
  start: (a, item) => { a.journalIn = item.journalIn; },
};

const prefixOk = (a, out) => {
  const ok = a.journalIn.length <= out.length && a.journalIn.every((e, i) => same(e, out[i]));
  return ok ? null : fail('journalIn is not a prefix of journalOut');
};

const orderOk = (a, out, byIdx) => {
  const issued = a.iss.filter((i) => i.pos <= a.cut);
  const notCmd = issued.find((i) => byIdx[i.idx] && byIdx[i.idx].e !== 'cmd');
  if (notCmd) return fail('issue names a journal entry that is no command', notCmd);
  const persisted = issued.filter((i) => byIdx[i.idx]?.e === 'cmd').map((i) => i.idx);
  const all = out.filter((e) => e.e === 'cmd' && !(e.cmd.c === 'cancelCall' && e.cmd.by === 'sdk'))
    .map((e) => e.idx);
  if (!(persisted.length <= all.length && persisted.every((v, i) => v === all[i]))) {
    return fail('issued commands are not the journal commands in order');
  }
  const inSet = new Set(a.journalIn.map((e) => e.idx));
  const missing = all.find((idx) => !inSet.has(idx) && !persisted.includes(idx));
  return missing === undefined ? null : fail('journal command not issued by this attempt', { idx: missing });
};

const issuerStable = (a, x, byIdx) => {
  const bad = a.iss.find((i) => {
    const c = byIdx[i.idx]?.e === 'cmd' ? byIdx[i.idx].cmd : null;
    return x.firsts.some((first) => {
      const f = first[i.idx];
      return f && f.cmd && c && same(f.cmd, c) && f.fiber !== i.fiber;
    });
  });
  return bad ? fail('replay issues a journal command from another fiber', bad) : null;
};

// =====================================================================
// S4: one race; only its members consumed, none skipped; one delivery a turn.
// Kept: the consumed entries' indices with their positions and kinds, the
// positions of each command's issue, each operation's first delivery and
// release, the executor's cancels, deadline pairing, and the open turn's
// delivery count. Skips are judged at attemptEnd, the first moment the
// stream shows entries the race never consumed.

const deadlinePairing = (a, e, P) => {
  // A deadline sleep pairs with the latest earlier unpaired run that declares
  // a deadline, else with the next such run issued.
  if (e.t !== 'issue' || !e.cmd) return;
  const isDeadlineRun = e.cmd.c === 'run' && P.ops[e.cmd.op]?.deadline !== undefined;
  if (e.cmd.c === 'sleep' && e.cmd.op === 'deadline') {
    const run = a.freeRuns.filter((r) => r.idx < e.cmdIdx).at(-1);
    if (run) {
      a.freeRuns = a.freeRuns.filter((r) => r !== run);
      a.deadlineOf[e.cmdIdx] = run.op;
    } else a.waitingDeadlines.push(e.cmdIdx);
  }
  if (isDeadlineRun && !a.pairedRuns.includes(e.cmd.op)) {
    a.pairedRuns.push(e.cmd.op);
    const d = a.waitingDeadlines.shift();
    if (d !== undefined) a.deadlineOf[d] = e.cmd.op;
    else a.freeRuns.push({ idx: e.cmdIdx, op: e.cmd.op });
  }
};
const pairingState = () => ({ freeRuns: [], waitingDeadlines: [], pairedRuns: [], deadlineOf: {} });
const PAIRING_MUT = ['freeRuns', 'waitingDeadlines', 'pairedRuns', 'deadlineOf'];

const firstPos = (map, key) => (key in map ? map[key] : Infinity);

const S4 = {
  mut: { issue: [...PAIRING_MUT, 'issuedAt', 'cancelAt'], deliver: ['delAt'], release: ['relAt'],
    consume: ['consIdx', 'cons', 'resultAt'] },
  fresh: () => ({ ...pairingState(), issuedAt: {}, cons: [], consIdx: {}, resultAt: {},
    delAt: {}, relAt: {}, cancelAt: {}, segDels: 0 }),
  event: (a, e, P) => {
    deadlinePairing(a, e, P);
    if (e.t === 'turn') a.segDels = 0;
    if (e.t === 'issue') {
      if (!(e.cmdIdx in a.issuedAt)) a.issuedAt[e.cmdIdx] = e.pos;
      if (e.cmd?.c === 'cancelCall' && e.cmd.by === 'executor' && !(e.cmd.target in a.cancelAt)) {
        a.cancelAt[e.cmd.target] = e.pos;
      }
    }
    if (e.t === 'deliver') {
      if (!(e.op in a.delAt)) a.delAt[e.op] = e.pos;
      if (e.pos < closing(a) && a.seg) {
        a.segDels += 1;
        if (a.segDels > 1) hit(a, fail('two results delivered in one turn', { pos: e.pos }));
      }
    }
    if (e.t === 'release' && !(e.op in a.relAt)) a.relAt[e.op] = e.pos;
    if (e.t === 'consume') consumeS4(a, e);
  },
  end: (a, item) => skippedMember(a, item.journalOut),
};

const consumeS4 = (a, e) => {
  if (e.entryIdx in a.consIdx) hit(a, fail('entry consumed twice', { idx: e.entryIdx }));
  else a.consIdx[e.entryIdx] = e.pos;
  const cls = classify(a, e.entry);
  a.cons.push({ pos: e.pos, idx: e.entryIdx });
  if (cls.k === 'result' && ['run', 'call', 'attach'].includes(cls.c) && !(cls.op in a.resultAt)) {
    a.resultAt[cls.op] = e.pos;
  }
  const nonMember = cls.k === 'deadline'
    ? a.deadlineOf[e.entry.of] !== undefined && firstPos(a.resultAt, a.deadlineOf[e.entry.of]) < e.pos
    : cls.k === 'result' && cls.c !== 'run'
      && (firstPos(a.relAt, cls.op) < e.pos || firstPos(a.cancelAt, e.entry.of) < e.pos);
  if (nonMember) pend(a, e.pos, fail('race consumed a result of an operation in no set', { idx: e.entryIdx }));
};

const memberAt = (a, entry, t, journal) => {
  if (!(firstPos(a.issuedAt, entry.of) < t)) return false;
  const cmd = journalCmd(journal, entry.of);
  if (!cmd) return false;
  if (isId(entry.value) || (cmd.c === 'run')) return true;
  if (cmd.c === 'sleep' && cmd.op === 'deadline') {
    const run = a.deadlineOf[entry.of];
    const rn = run !== undefined ? runResult(journal, run) : null;
    return run !== undefined && !(firstPos(a.resultAt, run) < t) && !(rn && rn.idx < entry.idx);
  }
  return (a.rootExit ?? Infinity) > t && !(firstPos(a.delAt, cmd.op) < t)
    && !(firstPos(a.relAt, cmd.op) < t) && !(firstPos(a.cancelAt, entry.of) < t);
};

const skippedMember = (a, journal) => {
  const bad = a.cons.filter((c) => c.pos <= a.cut).find((c) => journal.some((e) =>
    e.e === 'notif' && e.idx < c.idx && !(firstPos(a.consIdx, e.idx) < c.pos)
    && memberAt(a, e, c.pos, journal)));
  return bad ? fail('race consumed an entry past a member it skipped', bad) : null;
};

// =====================================================================
// S6: no blocked-handler violation while something is pending; quiet while
// frozen. Kept: the runs issued whose result is unconsumed, the calls and
// sends whose id is unconsumed, the consumed causes not yet taken by a turn
// (cancels count only before the root's exit and the freeze), and for each
// blocked violation the results then queued that a later turn could name.

const FREEZE_OK = new Set(['consume', 'abort', 'warn', 'done', 'settle', 'propose', 'wrapper']);

const quietFrozen = (a, e) => {
  if (a.freeze === null || e.pos <= a.freeze) return;
  if (!FREEZE_OK.has(e.t)) pend(a, e.pos, fail('executor acted while frozen', { t: e.t, pos: e.pos }));
  else if (e.t === 'abort' && e.cause !== 'deadline') pend(a, e.pos, fail('non-deadline abort while frozen'));
};

const S6 = {
  mut: { issue: ['openRuns', 'openIds'], consume: ['queued'], violation: ['watch'] },
  fresh: () => ({ openRuns: [], openIds: [], queued: [], watch: [] }),
  event: (a, e) => {
    quietFrozen(a, e);
    if (e.t === 'issue' && e.cmd?.c === 'run') a.openRuns.push(e.cmdIdx);
    if (e.t === 'issue' && ['call', 'send'].includes(e.cmd?.c)) a.openIds.push(e.cmdIdx);
    if (e.t === 'consume' && e.entry?.e === 'notif') {
      if (isId(e.entry.value)) a.openIds = a.openIds.filter((i) => i !== e.entry.of);
      else a.openRuns = a.openRuns.filter((i) => i !== e.entry.of);
    }
    if (e.t === 'consume') {
      const cancelCause = e.entry?.e === 'cancel' && a.rootExit === null && a.freeze === null;
      a.queued.push({ idx: e.entryIdx, cancel: cancelCause });
    }
    if (e.t === 'turn' && e.cause === 'journal') {
      if (a.watch.includes(e.entryIdx)) hit(a, fail('blocked-handler violation while a cause was queued'));
      a.queued = a.queued.filter((q) => q.idx !== e.entryIdx);
    }
    if (e.t === 'violation' && e.kind === 'blocked') blockedAt(a, e);
  },
};

const blockedAt = (a, e) => {
  if (a.openRuns.length || a.openIds.length || a.queued.some((q) => q.cancel)) {
    hit(a, fail('blocked-handler violation while something is pending', { pos: e.pos }));
  }
  a.watch.push(...a.queued.map((q) => q.idx));
};

// =====================================================================
// S7: one cause per turn, the head of the cause queue.
// Kept: whether a first turn was seen, the last cause index taken, the
// cause queue (consumed entries not yet taken, with their kind, operation,
// and whether a cancel was consumed before the root's exit and the freeze),
// the released operations, and the open turn's summary.

const S7 = {
  mut: { release: ['rel'], consume: ['queue'], turn: ['taken'] },
  fresh: () => ({ firsts: 0, lastCause: null, queue: [], taken: [], rel: [] }),
  event: (a, e) => {
    if (e.t === 'release' && !a.rel.includes(e.op)) a.rel.push(e.op);
    if (e.t === 'consume') {
      const cls = classify(a, e.entry);
      a.queue.push({ idx: e.entryIdx, k: cls.k, op: cls.op ?? null,
        early: a.rootExit === null && a.freeze === null });
    }
    if (e.t === 'turn') turnS7(a, e);
    if (e.t === 'deliver' && e.pos < closing(a) && a.seg?.cause !== 'journal') {
      hit(a, fail('delivery outside a journal turn', { pos: e.pos }));
    }
  },
  turnEnd: (a, seg, P, x, nextPos) => {
    if (seg.cause !== 'journal' || !seg.causeEntry) return;
    const c = seg.causeEntry;
    if (seg.dels.length > 1) { hit(a, fail('two deliveries in one turn', { turn: seg.start })); return; }
    const ok = c.k === 'cancel' ? seg.dels.length === 0
      : (seg.dels.length === 1 && seg.dels[0].op === c.op)
        || (seg.dels.length === 0 && seg.issues.some((i) => i.c === 'sleep' && i.op === c.op));
    if (!ok) pend(a, completeFrom(seg, nextPos), fail('turn did not act on the head of the cause queue', { turn: seg.start }));
  },
};

const turnS7 = (a, e) => {
  if (e.cause === 'first') {
    a.firsts += 1;
    if (a.firsts > 1) hit(a, fail('two first turns'));
  } else if (a.nSeg === 1) hit(a, fail('the first turn has another cause'));
  if (e.cause === 'local' && e.pos < closing(a)) pend(a, e.pos, fail('local turn while the attempt is open'));
  if (e.cause !== 'journal') return;
  if (e.pos >= closing(a)) { hit(a, fail('journal turn during closing')); return; }
  if (e.entryIdx === undefined) { hit(a, fail('journal turn names no cause')); return; }
  if (a.lastCause !== null && !(e.entryIdx > a.lastCause)) hit(a, fail('turns took causes out of queue order'));
  a.lastCause = e.entryIdx;
  const skipped = a.queue.find((q) => q.idx < e.entryIdx && !a.taken.includes(q.idx)
    && ((q.k === 'cancel' && q.early) || (q.k === 'result' && !a.rel.includes(q.op))));
  if (skipped) hit(a, fail('turn skipped a queued cause', { turn: e.pos, skipped: skipped.idx }));
  const cause = a.queue.find((q) => q.idx === e.entryIdx) ?? null;
  a.taken.push(e.entryIdx);
  if (!cause) { hit(a, fail('turn names an entry not consumed before it')); return; }
  if (!['cancel', 'result'].includes(cause.k)) { hit(a, fail('turn caused by an entry that is no cause')); return; }
  a.seg.causeEntry = cause;
};

// =====================================================================
// S8: the clock. Kept: whether an overflow violation voids the attempt,
// the largest and first applied samples, the upper bound on L so far, the
// open sleep links of each operation (length, anchor, and the turn and true
// time that issued them), the open turn's candidate exact anchor, and, for
// P5, the reads (L, last true time, links credited) and the running E and
// lead. Every failure is held until attemptEnd, where an overflow voids it.

const MAX_LINK = 2 ** 31 - 1;

const clockFresh = () => ({ overflow: false, maxS: null, firstS: null, bound: null, lastTrue: null,
  links: {}, credited: 0, segL: null, segSettled: null, unanchored: [],
  reads: [], E: 0, lead: 0, noLead: false, ttDown: false, releasedSleep: false });

// Exact anchor: the first clock read in a turn after its last sample and
// delivery. Links issued in the turn take it when the turn closes, else the
// bound at their issue.
const clockEvent = (a, e, P) => {
  if (e.t === 'violation' && e.kind === 'overflow') a.overflow = true;
  if (e.t === 'turn') { closeAnchors(a); a.segSettled = -1; a.segFirstTrue = null; }
  if (e.t === 'sample') {
    if (a.segFirstTrue === null || a.segFirstTrue === undefined) a.segFirstTrue = e.trueTime;
    if (a.lastTrue !== null && e.trueTime < a.lastTrue) a.ttDown = true;
    a.maxS = Math.max(a.maxS ?? -Infinity, e.reading);
    a.firstS ??= e.reading;
    a.bound = Math.max(a.bound ?? -Infinity, e.reading);
    a.lastTrue = e.trueTime;
    a.E = Math.max(a.E, e.reading - e.trueTime);
    a.segSettled = e.pos;
    a.segL = null;
  }
  if (e.t === 'deliver') {
    a.segSettled = e.pos;
    a.segL = null;
    if (a.links[e.op]) credit(a, e.op);
  }
  if (e.t === 'issue' && e.cmd?.c === 'sleep' && e.cmd.op !== 'deadline') {
    credit(a, e.cmd.op);
    const link = { ms: e.cmd.ms, anchor: null, boundAt: a.bound, issueTrue: a.segFirstTrue ?? null };
    (a.links[e.cmd.op] ??= []).push(link);
    a.unanchored.push({ op: e.cmd.op, i: a.links[e.cmd.op].length - 1 });
  }
  if (e.t === 'clock' && a.segSettled !== null && a.segSettled !== undefined && a.segL === null) a.segL = e.L;
};

const closeAnchors = (a) => {
  a.unanchored.forEach(({ op, i }) => {
    const link = a.links[op]?.[i];
    if (link && link.anchor === null) link.anchor = a.segL ?? link.boundAt;
  });
  a.unanchored = [];
  a.segL = null;
};

const credit = (a, op) => {
  const open = a.links[op] ?? [];
  open.forEach((link) => {
    const anchor = link.anchor ?? a.segL ?? link.boundAt;
    a.bound = Math.max(a.bound ?? -Infinity, anchor + link.ms);
    a.credited += 1;
    if (link.issueTrue === null || a.segFirstTrue === null || a.segFirstTrue === undefined) a.noLead = true;
    else a.lead = Math.max(a.lead, link.ms - (a.segFirstTrue - link.issueTrue));
  });
  a.links[op] = [];
};

const CLOCK_MUT = { turn: ['links:3'], issue: ['links:3', 'unanchored', 'sl:2', 'ownIssued'], deliver: ['links:3'],
  clock: ['reads'], consume: ['consumedOf'], release: ['rel'] };
const clockMonitor = (id, check) => monitor(id, {
  mut: CLOCK_MUT,
  fresh: clockFresh,
  event: (a, e, P) => {
    if (e.t === 'turn') a.segHasSample = false;
    if (e.t === 'sample') a.segHasSample = true;
    clockEvent(a, e, P);
    check.event?.(a, e, P);
  },
  turnEnd: check.turnEnd,
  voids: (a) => a.overflow,
  deferHits: true,
  end: (a, item, P) => a.clockFail ?? check.end?.(a, item, P) ?? null,
});

const clockFail = (a, f) => { if (!a.clockFail) a.clockFail = f; };

const P2 = clockMonitor('S8.P2', {
  event: (a, e) => {
    if (e.t !== 'clock') return;
    if (a.lastL !== undefined && e.L < a.lastL) clockFail(a, fail('L decreased'));
    a.lastL = e.L;
  },
});

const P4 = clockMonitor('S8.P4', {
  event: (a, e) => {
    if (e.t === 'clock' && a.maxS !== null && e.L < a.maxS) clockFail(a, fail('L below an applied sample'));
  },
});

const withinBound = (a, L) => {
  if (!Number.isInteger(L)) return fail('L is not an integer');
  if (a.firstS !== null && L < a.firstS) return fail('L below the first sample');
  return L > a.bound ? fail('L above max(samples, anchor + d of credited links)', { L, bound: a.bound }) : null;
};

const P6 = clockMonitor('S8.P6', {
  event: (a, e) => {
    if (e.t !== 'clock' || a.maxS === null) return;
    const f = withinBound(a, e.L);
    if (f) clockFail(a, f);
  },
});

const P5 = clockMonitor('S8.P5', {
  event: (a, e) => {
    if (e.t === 'clock' && a.maxS !== null) {
      a.reads.push({ L: e.L, lastTrue: a.lastTrue, credited: a.credited });
    }
  },
  end: (a) => {
    if (a.ttDown || a.noLead) return null;
    const E = Math.max(0, a.E);
    const lead = Math.max(0, a.lead);
    const bad = a.reads.find((r) => r.L > r.lastTrue + E + lead * r.credited);
    return bad ? fail('L above true time + E + leads', bad) : null;
  },
});

// P3: the links of a delivered sleep sum to its rounded duration, each in
// range, each issued after the previous one was consumed and its turn
// sampled. Kept per sleep: the sum and count of its links, whether a link
// broke the order, and the last link's index; and the results consumed.
const P3 = clockMonitor('S8.P3P9', {
  event: (a, e, P) => {
    a.sl ??= {};
    a.consumedOf ??= [];
    if (e.t === 'consume' && e.entry?.e === 'notif') a.consumedOf.push(e.entry.of);
    if (e.t === 'issue' && e.cmd?.c === 'sleep' && e.cmd.op !== 'deadline') {
      const s = (a.sl[e.cmd.op] ??= { sum: 0, n: 0, bad: false, last: null, range: false });
      if (s.last !== null && !(a.consumedOf.includes(s.last) && a.segHasSample)) s.bad = true;
      s.sum += e.cmd.ms;
      s.n += 1;
      s.last = e.cmdIdx;
      if (e.cmd.ms < 1 || e.cmd.ms > MAX_LINK) s.range = true;
    }
    if (e.t === 'deliver' && P.ops[e.op]?.s === 'sleep') {
      const s = a.sl[e.op] ?? { sum: 0, n: 0, bad: false, range: false };
      const rounded = Math.ceil(P.ops[e.op].ms);
      if (s.sum !== rounded) clockFail(a, fail('links do not sum to the duration', { op: e.op }));
      else if (rounded > 0 && s.range) clockFail(a, fail('link length out of range'));
      else if (s.bad) clockFail(a, fail('next link issued before the previous link was credited'));
    }
  },
});

// P7: each delivery before closing follows a sample its own turn issued.
// Kept: the samples issued in the open turn and whether one was applied.
const P7 = clockMonitor('S8.P7', {
  event: (a, e) => {
    if (e.t === 'turn') { a.ownIssued = []; a.firstSample = null; }
    if (e.t === 'issue') (a.ownIssued ??= []).push(e.cmdIdx);
    if (e.t === 'sample' && a.seg && a.firstSample === null) {
      a.firstSample = { own: (a.ownIssued ?? []).includes(e.cmdIdx) };
      a.ownApplied = a.firstSample.own;
    }
    if (e.t === 'deliver' && e.pos < closing(a) && !(a.seg && a.firstSample?.own)) {
      clockFail(a, fail('delivery without a sample of its own turn'));
    }
  },
});

// P8: one sample per journal or first turn, issued by it; none in a local
// turn; a released operation never delivered or continued; and reads after
// a released sleep within the P6 bound. Kept: the released operations, the
// open turn's summary, and the first failure pending on the cut.
const P8 = clockMonitor('S8.P8', {
  event: (a, e, P) => {
    a.rel ??= [];
    if (e.t === 'release' && !a.rel.includes(e.op)) {
      a.rel.push(e.op);
      if (P.ops[e.op]?.s === 'sleep') a.releasedSleep = true;
    }
    const late = (e.t === 'deliver' && a.rel.includes(e.op))
      || (e.t === 'issue' && e.cmd?.c === 'sleep' && e.cmd.op !== 'deadline' && a.rel.includes(e.cmd.op));
    if (late) clockFail(a, fail('released operation delivered or continued'));
    if (e.t === 'clock' && a.releasedSleep && a.maxS !== null) {
      const f = withinBound(a, e.L);
      if (f) clockFail(a, f);
    }
  },
  turnEnd: (a, seg, P, x, nextPos) => {
    const n = seg.samples.length;
    if (seg.cause === 'local') {
      if (n) pend(a, seg.start, fail('local turn sampled'));
      return;
    }
    if (n > 1) pend(a, seg.start, fail('turn without exactly one sample'));
    if (n === 0) pend(a, nextPos, fail('turn without exactly one sample'));
    const own = seg.samples.every((s) => seg.issues.some((i) => i.idx === s.cmdIdx));
    if (!own) pend(a, seg.start, fail('turn applied a sample another turn issued'));
  },
});

// =====================================================================
// S11: only race members awaited; closing issues only cancels.
// Kept: the commands issued so far, the released operations, the issues
// that were not executor cancels (index and position: whether they were
// after the cut, and persisted, is known only at attemptEnd), and whether
// a delivery came after closing and whether a refused start was recorded.

const S11 = {
  mut: { issue: ['issued', 'others'], release: ['rel'] },
  fresh: () => ({ issued: [], rel: [], others: [], lateDeliver: false, refused: false }),
  event: (a, e) => {
    if (e.t === 'issue') {
      a.issued.push(e.cmdIdx);
      if (!(e.cmd?.c === 'cancelCall' && e.cmd.by === 'executor')) {
        a.others.push({ pos: e.pos, idx: e.cmdIdx, closing: e.pos >= closing(a) });
      }
    }
    if (e.t === 'consume' && e.entry?.e === 'notif' && !a.issued.includes(e.entry.of)) {
      hit(a, fail('race awaited a command this attempt had not issued', { idx: e.entryIdx }));
    }
    if (e.t === 'release' && !a.rel.includes(e.op)) a.rel.push(e.op);
    if (e.t === 'deliver' && a.rel.includes(e.op)) hit(a, fail('result of a retired handle reached a fiber'));
    if (e.t === 'deliver' && e.pos >= closing(a)) a.lateDeliver = true;
    if (e.t === 'violation' && e.kind === 'refusedAtClosing') a.refused = true;
  },
  end: (a, item) => closingIssuesOnlyCancels(a, item.journalOut)
    ?? (a.lateDeliver && !a.refused ? fail('delivery after closing latched') : null),
};

const closingIssuesOnlyCancels = (a, journal) => {
  const bad = a.others.find((o) => (o.closing || o.pos > a.cut) && journalCmd(journal, o.idx)
    && !(journalCmd(journal, o.idx).c === 'cancelCall' && journalCmd(journal, o.idx).by === 'executor'));
  return bad ? fail('command issued after closing latched', bad) : null;
};

// =====================================================================
// S12: journal order. Kept: the last consumed index, the unmatched consumed
// results of each operation (index and value), the last delivered index,
// the released operations, the first cancel consumed as a cause, whether
// the root's cancel interrupt has happened, and the deliveries before
// closing (position and index), judged against the cancel at attemptEnd.

const S12 = {
  mut: { release: ['rel'], consume: ['results:2', 'consumedRes'], deliver: ['results', 'dels'] },
  fresh: () => ({ lastIdx: null, results: {}, lastDel: null, rel: [], firstCancel: null,
    rootCancel: null, dels: [], turnCause: null }),
  event: (a, e, P) => {
    if (e.t === 'release' && !a.rel.includes(e.op)) a.rel.push(e.op);
    if (e.t === 'consume') consumeS12(a, e);
    if (e.t === 'turn') a.turnCause = e.cause === 'journal' ? e.entryIdx ?? null : null;
    if (e.t === 'turn' && e.cause === 'journal') {
      const c = a.consumedRes?.[e.entryIdx];
      if (c && a.rel.includes(c.op)) hit(a, fail('turn for a result whose fiber stopped awaiting it'));
    }
    if (e.t === 'interrupt' && e.fiber === P.root && e.cause === 'cancel' && a.rootCancel === null) a.rootCancel = e.pos;
    if (e.t === 'deliver') deliverS12(a, e);
  },
  end: (a) => {
    if (a.firstCancel === null || a.rootCancel === null) return null;
    const bad = a.dels.find((d) => (d.idx < a.firstCancel) !== (d.pos < a.rootCancel));
    return bad ? fail('root interrupted out of journal order', bad) : null;
  },
};

const consumeS12 = (a, e) => {
  if (a.lastIdx !== null && e.entryIdx <= a.lastIdx) pend(a, e.pos, fail('entries consumed out of journal order'));
  a.lastIdx = e.entryIdx;
  const cls = classify(a, e.entry);
  a.consumedRes ??= {};
  if (cls.k === 'result') {
    (a.results[cls.op] ??= []).push({ idx: e.entryIdx, value: e.entry.value });
    a.consumedRes[e.entryIdx] = { op: cls.op, value: e.entry.value };
  }
  if (cls.k === 'cancel' && a.firstCancel === null && a.rootExit === null && a.freeze === null) {
    a.firstCancel = e.entryIdx;
  }
};

const deliverS12 = (a, e) => {
  if (isId(e.value)) hit(a, fail('invocation id delivered to a fiber'));
  if (e.op === 'deadline') hit(a, fail('deadline completion delivered'));
  if (a.rel.includes(e.op)) hit(a, fail('result delivered after its fiber stopped awaiting it'));
  const fromTurn = a.turnCause !== null && a.consumedRes?.[a.turnCause]?.op === e.op
    ? { idx: a.turnCause, value: a.consumedRes[a.turnCause].value } : null;
  const list = a.results[e.op] ?? [];
  const match = fromTurn ?? list.at(-1) ?? null;
  a.results[e.op] = list.filter((r) => r.idx !== match?.idx);
  if (e.pos >= closing(a)) return;
  if (!match) { hit(a, fail('delivery of a result the race never consumed')); return; }
  if (!same(e.value, match.value)) hit(a, fail('delivered value differs from the journal'));
  if (a.lastDel !== null && match.idx < a.lastDel) hit(a, fail('results delivered out of journal order'));
  a.lastDel = match.idx;
  a.dels.push({ pos: e.pos, idx: match.idx });
};

// =====================================================================
// S13: one cancellation, one interruption of the root. Kept: whether a
// cancel was consumed, how many cancel turns began (the open turn's being
// the first or a later one), whether the root was interrupted by the
// cancellation, the first cancel turn's summary until it is judged.

const S13 = {
  mut: { issue: ['maxRefs', 'issuedAt'], consume: ['maxRefs', 'signals', 'queueKinds'] },
  fresh: () => ({ cancelSeen: false, cancelTurns: 0, rootCancels: 0, firstSeg: null, inFirst: false,
    inLater: false, consumedCancel: false, queueKinds: {}, signals: [], maxRefs: [], issuedAt: {} }),
  start: (a, item) => { a.journalIn = item.journalIn; },
  event: (a, e, P) => {
    // For attributing SDK cancels: the consumed signals' positions, each
    // command's first issue, and where the largest journal index named so
    // far grew.
    const ref = e.t === 'issue' ? e.cmdIdx : e.t === 'consume' ? e.entryIdx : null;
    if (ref !== null && (a.maxRefs.length === 0 || ref > a.maxRefs.at(-1).idx)) a.maxRefs.push({ pos: e.pos, idx: ref });
    if (e.t === 'issue' && !(e.cmdIdx in a.issuedAt)) a.issuedAt[e.cmdIdx] = e.pos;
    if (e.t === 'consume' && e.entry?.e === 'cancel') a.signals.push(e.pos);
    if (e.t === 'consume') {
      a.queueKinds[e.entryIdx] = e.entry?.e === 'cancel';
      if (e.entry?.e === 'cancel') a.consumedCancel = true;
    }
    if (e.t === 'turn') turnS13(a, e);
    if (e.t === 'issue' && a.consumedCancel && P.ops[e.cmd?.op]?.s === 'call' && e.cmd.c === 'call') {
      hit(a, fail('call issued after a cancel signal was consumed is not a send'));
    }
    if (a.inLater && (['deliver', 'interrupt', 'clock', 'draw'].includes(e.t)
      || (e.t === 'issue' && e.cmd?.op !== 'sample'))) {
      hit(a, fail('a later cancel signal changed what handler code observes'));
    }
    if (e.t === 'interrupt' && e.cause === 'cancel') interruptS13(a, e, P);
    if (a.rootExit !== null && e.pos > a.rootExit) {
      if (e.t === 'turn' && e.cause === 'journal') hit(a, fail('turn after the root exited'));
      if (e.t === 'sample') hit(a, fail('sample after the root exited'));
    }
  },
  turnEnd: (a, seg, P, x, nextPos) => {
    if (a.firstSeg === seg.k && a.rootCancels === 0) {
      pend(a, completeFrom(seg, nextPos), fail('first cancel turn did not interrupt the root'));
    }
  },
  end: (a, item) => sdkCancels(a, item.journalOut),
};

const turnS13 = (a, e) => {
  const isCancel = e.cause === 'journal' && a.queueKinds[e.entryIdx] === true;
  a.inFirst = false;
  a.inLater = false;
  if (!isCancel) return;
  a.cancelTurns += 1;
  if (a.cancelTurns === 1) { a.firstSeg = a.nSeg; a.inFirst = true; } else a.inLater = true;
};

const interruptS13 = (a, e, P) => {
  if (e.fiber === P.root) a.rootCancels += 1;
  if (a.rootCancels > 1) hit(a, fail('root interrupted by cancellation twice'));
  if (!a.inFirst) hit(a, fail('cancellation interrupt outside the first cancel turn'));
  if (P.daemon[e.fiber]) hit(a, fail('cancellation interrupted a daemon fiber'));
  if (a.rootExit !== null) hit(a, fail('cancellation interrupt after the root exited'));
};

// An SDK cancel new in this attempt belongs to the last signal consumed
// before the first event naming a later journal index; one belonging to
// the k-th signal (k >= 2) must not target a call issued before signal k-1.
const sdkCancels = (a, journal) => {
  const inSet = new Set(a.journalIn.map((e) => e.idx));
  const bad = journal.find((e) => {
    if (e.e !== 'cmd' || e.cmd.c !== 'cancelCall' || e.cmd.by !== 'sdk') return false;
    if (journalCmd(journal, e.cmd.target)?.c !== 'call') return true;
    if (inSet.has(e.idx)) return false;
    const point = a.maxRefs.find((r) => r.idx > e.idx)?.pos ?? Infinity;
    const k = a.signals.filter((pos) => pos < point).length;
    const issued = a.issuedAt[e.cmd.target] ?? -Infinity;
    return k >= 2 && issued < a.signals[k - 2];
  });
  return bad ? fail('a later cancel signal made the SDK cancel a call', bad) : null;
};

// =====================================================================
// S14a: after the root's cancel interrupt and before its exit, no refused
// start, and every command issued then is journaled (output or suspension).
// Kept: whether the root was interrupted by cancellation and the indices of
// the commands issued in that window.

const S14a = {
  mut: { issue: ['window'] },
  fresh: () => ({ cancelled: false, window: [] }),
  event: (a, e, P) => {
    if (e.t === 'interrupt' && e.fiber === P.root && e.cause === 'cancel') a.cancelled = true;
    const open = a.cancelled && a.rootExit === null;
    if (open && e.t === 'violation' && e.kind === 'refusedAtClosing' && a.viol === e.pos) {
      hit(a, fail('finalizer start refused while the attempt was open'));
    }
    if (open && e.t === 'issue' && !(e.t === 'interrupt')) a.window.push(e.cmdIdx);
  },
  end: (a, item) => {
    if (!['output', 'suspended'].includes(a.endKind)) return null;
    const lost = a.window.find((idx) => !journalCmd(item.journalOut, idx));
    return lost !== undefined ? fail('finalizer command not journaled', { idx: lost }) : null;
  },
};

// =====================================================================
// S14b: calls after a consumed cancel are sends keyed <invocation id>:<n>.
// Kept across attempts: every send's key with its index, and the ids seen.

const sendChecks = (journal) => {
  let n = 0;
  return journal.filter((e) => e.e === 'cmd').map((e) => {
    const me = e.cmd.c === 'send' ? { idx: e.idx, key: e.cmd.key, n } : null;
    if (['run', 'sleep', 'call', 'send', 'attach'].includes(e.cmd.c)) n += 1;
    return me;
  }).filter(Boolean);
};

const keyOk = (s) => {
  const cut = typeof s.key === 'string' ? s.key.lastIndexOf(':') : -1;
  return cut >= 1 && s.key.slice(cut + 1) === String(s.n);
};

const S14b = {
  x0: () => ({ keys: {}, ids: [] }),
  fresh: () => ({ consumedCancel: false }),
  event: (a, e, P) => {
    if (e.t === 'consume' && e.entry?.e === 'cancel') a.consumedCancel = true;
    if (e.t === 'issue' && a.consumedCancel && P.ops[e.cmd?.op]?.s === 'call' && e.cmd.c === 'call') {
      hit(a, fail('call issued after a cancel signal was consumed is not a send'));
    }
  },
  end: (a, item, P, x) => {
    const sends = sendChecks(item.journalOut);
    const bad = sends.find((s) => !keyOk(s));
    if (bad) return fail('send key is not <invocation id>:<n>', bad);
    for (const s of sends) {
      if (s.key in x.keys && x.keys[s.key] !== s.idx) return fail('two sends share a key', s);
      x.keys[s.key] = s.idx;
      const id = s.key.slice(0, s.key.lastIndexOf(':'));
      if (!x.ids.includes(id)) x.ids.push(id);
    }
    return x.ids.length > 1 ? fail('send keys name different invocation ids') : null;
  },
  final: (x, item) => {
    const bad = (item.children ?? []).find((c) => c.kind === 'send'
      && Object.entries(x.keys).some(([k, idx]) => idx === c.viaCmd && k !== c.key));
    return bad ? fail('child key differs from its send', bad) : null;
  },
};

// =====================================================================
// S14d: a compensation's outcome reaches its finalizer; the child is never
// cancelled. Kept: whether the root was cancelled, each compensation send
// (index, key, owner, whether its owner was interrupted since, the attach
// result's value and whether it was delivered), and across attempts the
// compensation indices, the cancel targets and whether any attempt was killed.

const S14d = {
  mut: { issue: ['comps:2', 'attaches'], interrupt: ['comps:2'], consume: ['comps:2'], deliver: ['comps:2'] },
  x0: () => ({ comps: [], targets: [], killed: false }),
  fresh: () => ({ rootCancelled: false, comps: [], attaches: {} }),
  event: (a, e, P) => {
    if (e.t === 'interrupt' && e.fiber === P.root && e.cause === 'cancel') a.rootCancelled = true;
    if (e.t === 'issue' && e.cmd?.c === 'send' && a.rootCancelled && !P.daemon[P.ops[e.cmd.op]?.fiber]) {
      a.comps.push({ idx: e.cmdIdx, key: e.cmd.key, op: e.cmd.op, owner: P.ops[e.cmd.op]?.fiber,
        interrupted: false, got: null, beforeExit: false, delivered: false });
    }
    if (e.t === 'issue' && e.cmd?.c === 'attach') a.attaches[e.cmdIdx] = e.cmd.target;
    if (e.t === 'interrupt') a.comps.forEach((c) => { if (c.owner === e.fiber && c.got === null) c.interrupted = true; });
    if (e.t === 'consume' && e.entry?.e === 'notif' && e.entry.of in a.attaches) {
      const c = a.comps.find((x) => x.key === a.attaches[e.entry.of]);
      if (c && c.got === null) { c.got = { value: e.entry.value }; c.beforeExit = a.rootExit === null; }
    }
    if (e.t === 'deliver' && a.rootExit === null) {
      a.comps.forEach((c) => { if (c.op === e.op && c.got && same(c.got.value, e.value)) c.delivered = true; });
    }
  },
  end: (a, item, P, x) => {
    const journal = item.journalOut;
    x.targets.push(...journal.filter((e) => e.e === 'cmd' && e.cmd.c === 'cancelCall').map((e) => e.cmd.target));
    if (a.endKind === 'killed') x.killed = true;
    x.comps.push(...a.comps.map((c) => c.idx));
    const twice = a.comps.find((c) => journal.filter((e) => e.e === 'cmd' && e.cmd.c === 'attach'
      && e.cmd.target === c.key).length > 1);
    if (twice) return fail('compensation attached twice', twice);
    const lost = a.comps.find((c) => c.got && !c.interrupted && c.beforeExit && a.rootExit !== null && !c.delivered);
    return lost ? fail('finalizer did not receive the child outcome', lost) : null;
  },
  final: (x, item) => {
    const bad = x.comps.find((idx) => {
      const child = (item.children ?? []).find((c) => c.viaCmd === idx);
      return x.targets.includes(idx) || child?.cancelled || (child?.killed && !x.killed);
    });
    return bad !== undefined ? fail('compensation child cancelled', { send: bad }) : null;
  },
};

// =====================================================================
// S15: an interrupted fiber's uncompleted calls are cancelled, and no
// others. Kept: compensation sends, each call's issue (index, owner),
// completed operations, the fibers interrupted, the root's cancellation,
// cancelled calls, and the open cancel obligations (index, whether its id
// arrived, whether satisfied, the position it became due from).

const S15 = {
  mut: { issue: ['calls', 'comps', 'cancelled', 'owed:2'], interrupt: ['interrupted'],
    consume: ['done', 'idsIn', 'owed:2'], release: ['owed:2'] },
  fresh: () => ({ rootCancelled: false, comps: [], calls: {}, done: [], interrupted: [],
    cancelled: [], owed: [], seg409: false, segCancelInt: false }),
  event: (a, e, P) => {
    if (e.t === 'turn') { a.seg409 = false; a.segCancelInt = false; }
    if (e.t === 'interrupt') {
      if (!a.interrupted.includes(e.fiber)) a.interrupted.push(e.fiber);
      if (e.fiber === P.root && e.cause === 'cancel') a.rootCancelled = true;
      if (e.cause === 'cancel') a.segCancelInt = true;
    }
    if (e.t === 'issue' && ['call', 'send'].includes(e.cmd?.c) && !(e.cmd.op in a.calls)) {
      a.calls[e.cmd.op] = { idx: e.cmdIdx };
      if (e.cmd.c === 'send' && a.rootCancelled && !P.daemon[P.ops[e.cmd.op]?.fiber]) a.comps.push(e.cmdIdx);
    }
    if (e.t === 'consume') consumeS15(a, e);
    if (e.t === 'release' && P.ops[e.op]?.s === 'call') releaseS15(a, e);
    if (e.t === 'issue' && e.cmd?.c === 'cancelCall' && e.cmd.by === 'executor') cancelS15(a, e, P);
    if (e.t === 'deliver') {
      if (a.cancelled.includes(e.op)) hit(a, fail('a cancelled call\'s result reached a fiber'));
      if (e.value?.terminal === '409') a.seg409 = true;
    }
    if (a.seg409 && a.segCancelInt) hit(a, fail('a child\'s 409 became a cancellation'));
  },
  end: (a) => {
    const open = a.owed.find((o) => !o.ok && o.from <= a.cut);
    return open && a.endKind === 'output' ? fail('interrupted fiber\'s call not cancelled', open) : null;
  },
};

const consumeS15 = (a, e) => {
  const cls = classify(a, e.entry);
  if (cls.k === 'result' && ['run', 'call', 'attach'].includes(cls.c) && !a.done.includes(cls.op)) a.done.push(cls.op);
  a.owed.filter((o) => !o.ok && o.idReady && o.due).forEach((o) => {
    pend(a, e.pos, fail('interrupted fiber\'s call not cancelled', o));
    o.ok = true;
  });
  if (cls.k === 'id') {
    (a.idsIn ??= []).push(e.entry.of);
    a.owed.filter((o) => o.idx === e.entry.of && !o.idReady).forEach((o) => { o.idReady = true; o.due = true; });
  }
};

const releaseS15 = (a, e) => {
  const call = a.calls[e.op];
  if (!call || a.comps.includes(call.idx) || a.done.includes(e.op)) return;
  const idReady = a.idsIn?.includes(call.idx) ?? false;
  a.owed.push({ idx: call.idx, op: e.op, from: e.pos, idReady, due: idReady, ok: false });
};

const cancelS15 = (a, e, P) => {
  const target = cmdOf(a, e.cmd.target);
  const op = target?.op;
  if (!['call', 'send'].includes(target?.c)) { hit(a, fail('executor cancelled a non-call')); return; }
  if (a.comps.includes(e.cmd.target)) hit(a, fail('executor cancelled a compensation'));
  if (a.done.includes(op)) hit(a, fail('executor cancelled a completed call'));
  const owner = P.ops[op]?.fiber;
  const fine = a.interrupted.includes(owner) || (!P.daemon[owner] && a.rootCancelled) || closing(a) <= e.pos;
  if (!fine) hit(a, fail('executor cancelled a call of a fiber it did not interrupt'));
  if (!a.cancelled.includes(op)) a.cancelled.push(op);
  a.owed.filter((o) => o.idx === e.cmd.target && o.idReady).forEach((o) => { o.ok = true; });
};

// =====================================================================
// S16: run records by how an attempt ends.

const PERSISTED = ['output', 'suspended'];
const valueFits = (eff, v) => {
  if (eff.entered === false) return v?.terminal === ABORTED;
  if (eff.settled === 'ok') return !!v && 'ok' in v;
  if (eff.settled === 'terminal') return !!v && 'terminal' in v && v.terminal !== ABORTED;
  if (eff.settled === 'aborted') return v?.terminal === ABORTED;
  return false;
};

// S16a: in an output attempt every settled or refused run is journaled
// before Output. Kept: nothing from the trace.
const S16a = {
  end: (a, item) => {
    if (item.end.kind !== 'output') return null;
    const out = outputIdx(item.journalOut);
    const bad = item.effects.find((e) => (e.entered === false
      || (e.entered && ['ok', 'terminal', 'aborted'].includes(e.settled)))
      && !(runResult(item.journalOut, e.op)?.idx < out));
    return bad ? fail('settled run not journaled before output', bad) : null;
  },
};

// The runs an attempt owes the next one, and whether the next one paid:
// entered or refused the run, or journaled its terminal abort.
const rerunClaim = (owed) => ({
  x0: () => ({ prev: null }),
  end: (a, item, P, x) => {
    const effects = item.effects;
    const rerun = effects.find((e) => e.entered === true && runResult(a.journalIn, e.op));
    const prev = x.prev;
    x.prev = { n: a.n, owed: owed(item, a) };
    if (owed.rerunCheck && rerun) return fail('run with a journaled result executed again', rerun);
    if (!prev || a.n !== prev.n + 1 || item.end.kind !== 'output') return null;
    const paid = (op) => effects.some((e) => e.op === op && (e.entered === true || e.entered === false))
      || (runResult(item.journalOut, op)?.value?.terminal === ABORTED && !runResult(a.journalIn, op));
    const missing = prev.owed.find((op) => !paid(op));
    return missing ? fail('run whose result was not journaled did not execute again', { op: missing }) : null;
  },
  start: (a, item) => { a.journalIn = item.journalIn; },
});

const unjournaled = (kind) => Object.assign((item) => (item.end.kind === kind
  ? item.effects.filter((e) => e.entered && !runResult(item.journalOut, e.op)).map((e) => e.op) : []),
{ rerunCheck: true });

const S16d = rerunClaim(unjournaled('ended'));
const S16e = rerunClaim(unjournaled('crashed'));

// S16f: no attempt after a kill. Kept: whether an attempt was killed.
const S16f = {
  x0: () => ({ killed: false }),
  start: (a, item, P, x) => { if (x.killed) hit(a, fail('an attempt followed a kill')); },
  end: (a, item, P, x) => { if (item.end.kind === 'killed') x.killed = true; return null; },
};

// S16c: at suspension nothing executes and every settled or refused run
// is journaled with its outcome. Kept: nothing from the trace.
const S16c = {
  end: (a, item) => {
    if (item.end.kind !== 'suspended') return null;
    const bad = item.effects.find((e) => (e.entered && e.settled === null)
      || (e.entered !== null && !valueFits(e, runResult(item.journalOut, e.op)?.value)));
    return bad ? fail('suspension lost or left running a closure', bad) : null;
  },
};

// S16b: the freeze. Kept: the first retryable settle's position, the first
// retryable done (index, position), the closures done but not yet settled,
// the successes and terminal failures settled (index, position), each
// closure's first non-retryable proposal and the first retryable one, and
// across attempts the runs the attempt owes the next.
const S16bRerun = rerunClaim((item) => (item.end.kind === 'retry'
  ? item.effects.filter((e) => e.settled === 'retryable').map((e) => e.op) : []));

const S16b = {
  mut: { done: ['openDone'], settle: ['retryDone', 'settledOk'], propose: ['proposedOk'] },
  x0: S16bRerun.x0,
  start: S16bRerun.start,
  fresh: () => ({ firstRetrySettle: null, retryDone: null, openDone: [], settledOk: [],
    proposedOk: {}, firstRetryPropose: null, anySettle: false }),
  event: (a, e) => {
    quietFrozen(a, e);
    lifeS16b(a, e);
  },
  end: (a, item, P, x) => {
    const f = endS16b(a, item);
    const g = S16bRerun.end(a, item, P, x);
    return f ?? g;
  },
};

// Only a new turn (of any cause) may not come between a done and its settle:
// events of the turn in which the closure completed may follow it.
const DONE_GAP = new Set(['turn']);
const PREFIX_OK = new Set(['done', 'settle', 'propose', 'wrapper', 'consume', 'warn']);
const FROZEN_FORBIDS = new Set(['turn', 'deliver', 'issue', 'enter']);

const lifeS16b = (a, e) => {
  if (a.openDone.length && DONE_GAP.has(e.t)) pend(a, e.pos, fail('settlement held past an executor action'));
  if (e.t === 'done') {
    a.openDone.push(e.cmdIdx);
    if (e.outcome === 'retryable' && a.retryDone === null) a.retryDone = { idx: e.cmdIdx, pos: e.pos };
  }
  const s = a.firstRetrySettle;
  if (s !== null && e.pos > s) {
    if (e.t === 'deliver') pend(a, e.pos, fail('delivery after a retryable settle'));
    if (FROZEN_FORBIDS.has(e.t)) pend(a, e.pos, fail('executor acted after a retryable settle'));
    if (a.freeze === null && !PREFIX_OK.has(e.t) && e.t !== 'freeze') pend(a, e.pos, fail('freeze did not start at the retryable settle'));
  }
  if (e.t === 'freeze' && a.firstRetrySettle === null) a.freezeBeforeSettle = e.pos;
  if (e.t === 'settle') settleS16b(a, e);
  if (e.t === 'propose') {
    if (e.outcome === 'retryable') a.firstRetryPropose ??= e.pos;
    else if (!(e.cmdIdx in a.proposedOk)) a.proposedOk[e.cmdIdx] = e.pos;
  }
};

const settleS16b = (a, e) => {
  a.anySettle = true;
  a.openDone = a.openDone.filter((i) => i !== e.cmdIdx);
  if (e.outcome === 'retryable' && a.firstRetrySettle === null) a.firstRetrySettle = e.pos;
  // The first retryable done's settle must not come after another
  // retryable settle.
  if (a.retryDone && e.cmdIdx === a.retryDone.idx && !a.retryDone.settled) {
    a.retryDone.settled = true;
    if (a.firstRetrySettle !== null && a.firstRetrySettle < e.pos) {
      pend(a, Math.max(a.retryDone.pos, a.firstRetrySettle), fail('freeze did not start at the first retryable completion'));
    }
  }
  if (['ok', 'terminal'].includes(e.outcome) && !isSampleOp(e.op)) a.settledOk.push({ idx: e.cmdIdx, pos: e.pos });
};

const endS16b = (a, item) => {
  const s = a.firstRetrySettle !== null && a.firstRetrySettle <= a.cut ? a.firstRetrySettle : null;
  const frozen = a.freeze !== null && a.freeze <= a.cut;
  if (s === null && a.anySettle && frozen) return fail('freeze without a retryable settle before it');
  if (s !== null && a.freeze !== null && a.freeze < s) return fail('freeze before the first retryable settle');
  if (s !== null && !(a.freeze !== null && a.freeze > s && frozen) && !['crashed', 'killed'].includes(a.endKind)) {
    return fail('retryable settle not followed by a freeze before the end');
  }
  if (a.endKind === 'retry' && (a.firstRetryPropose !== null || Object.keys(a.proposedOk).length)) {
    const first = a.firstRetryPropose ?? Infinity;
    const bad = a.settledOk.filter((x) => x.pos <= a.cut).find((x) => !(a.proposedOk[x.idx] < first));
    if (bad) return fail('a settled outcome was not proposed before the retryable failure', bad);
  }
  const failed = item.effects.filter((e) => e.settled === 'retryable');
  if (a.freeze !== null && !failed.length) return fail('freeze with no retryable closure failure');
  return failed.length && PERSISTED.includes(item.end.kind)
    ? fail('attempt with a retryable closure failure was not retried') : null;
};

// =====================================================================
// S17: retained runs reach no fiber and leave the race only consumed.
// Kept: each run's release (position) unless its result was consumed
// first, deliveries after a release, and the consumed entries' indices
// with positions, judged against journalOut at attemptEnd.

const S17 = {
  mut: { consume: ['cons', 'resultIn'], release: ['retained'] },
  fresh: () => ({ retained: {}, resultIn: [], cons: {} }),
  event: (a, e, P) => {
    if (e.t === 'consume') {
      a.cons[e.entryIdx] ??= e.pos;
      const cls = classify(a, e.entry);
      if (cls.k === 'result' && ['run', 'call', 'attach'].includes(cls.c) && !a.resultIn.includes(cls.op)) a.resultIn.push(cls.op);
    }
    if (e.t === 'release' && P.ops[e.op]?.s === 'run' && !(e.op in a.retained) && !a.resultIn.includes(e.op)) {
      a.retained[e.op] = e.pos;
    }
    if (e.t === 'deliver' && e.op in a.retained) hit(a, fail('retained run delivered to a fiber'));
  },
  end: (a, item) => {
    const journal = item.journalOut;
    const out = outputIdx(journal);
    const bad = Object.keys(a.retained).find((op) => {
      const n = runResult(journal, op);
      const consumedOk = n && n.idx in a.cons && a.cons[n.idx] <= a.cut;
      const passed = n && Object.entries(a.cons).some(([idx, pos]) => Number(idx) > n.idx && pos <= a.cut);
      if (passed && !consumedOk) return true;
      return item.end.kind === 'output' && !(n && n.idx < out && consumedOk);
    });
    return bad ? fail('retained run left the race unconsumed or output came first', { op: bad }) : null;
  },
};

// =====================================================================
// S18: aborts only for their causes; failures classified by the record.
// Kept: each run's issue, release, interrupts of its owner since its issue,
// whether its result was consumed, its deadline's consumption, the aborts
// (operation and cause; for "ended", the first position), and the pairing
// of deadline sleeps with runs.

const S18 = {
  mut: { issue: [...PAIRING_MUT, 'runIssued'], interrupt: ['ownerHit'], release: ['rel', 'due'],
    consume: ['resultIn', 'deadlineAt'], abort: ['aborted'] },
  fresh: () => ({ ...pairingState(), runIssued: [], rel: {}, ownerHit: [], resultIn: [],
    deadlineAt: [], aborted: [], endedAbort: null, due: [] }),
  event: (a, e, P) => {
    deadlinePairing(a, e, P);
    if (e.t === 'issue' && e.cmd?.c === 'run') a.runIssued.push(e.cmd.op);
    if (e.t === 'interrupt') a.runIssued.filter((op) => P.ops[op]?.fiber === e.fiber && !a.ownerHit.includes(op)).forEach((op) => a.ownerHit.push(op));
    if (e.t === 'release' && !(e.op in a.rel)) {
      a.rel[e.op] = e.pos;
      if (P.ops[e.op]?.s === 'run' && !a.resultIn.includes(e.op)) a.due.push({ op: e.op, pos: e.pos });
    }
    if (e.t === 'consume') consumeS18(a, e);
    if (e.t === 'abort') abortS18(a, e, P);
  },
  end: (a, item) => {
    if (a.endedAbort !== null && !(a.endKind === 'ended' && a.endedAbort > a.cut)) return fail('ended abort without an Ended cut');
    const unaborted = a.due.find((d) => d.pos <= a.cut && !a.aborted.includes(d.op));
    if (unaborted) return fail('interrupted fiber\'s run not aborted', unaborted);
    const late = a.deadlineAt.find((d) => d.pos <= a.cut && d.due && !a.aborted.includes(d.op));
    if (late) return fail('run past its consumed deadline not aborted', late);
    return classifiedS18(a, item);
  },
};

const consumeS18 = (a, e) => {
  const cls = classify(a, e.entry);
  if (cls.k === 'result' && ['run', 'call', 'attach'].includes(cls.c) && !a.resultIn.includes(cls.op)) a.resultIn.push(cls.op);
  if (cls.k === 'deadline') {
    const op = a.deadlineOf[e.entry.of];
    if (op !== undefined && !a.deadlineAt.some((d) => d.op === op)) {
      a.deadlineAt.push({ op, pos: e.pos, due: !a.resultIn.includes(op) });
    }
  }
};

const abortS18 = (a, e, P) => {
  if (!a.aborted.includes(e.op)) a.aborted.push(e.op);
  if (P.ops[e.op]?.s !== 'run') { hit(a, fail('abort of something not a run')); return; }
  if (e.cause === 'ended') { a.endedAbort ??= e.pos; return; }
  if (e.cause === 'deadline') {
    const d = a.deadlineAt.find((x) => x.op === e.op);
    if (!d || !d.due) hit(a, fail('deadline abort without its cause'));
    return;
  }
  const ok = (e.op in a.rel || a.ownerHit.includes(e.op)) && !a.resultIn.includes(e.op);
  if (!ok) hit(a, fail('interrupt abort without an interrupt'));
};

const classifiedS18 = (a, item) => {
  const bad = item.effects.find((eff) => {
    const n = runResult(item.journalOut, eff.op);
    const fresh = n && !runResult(item.journalIn ?? a.journalIn ?? [], eff.op);
    if (!fresh || eff.entered === null || (eff.entered && eff.settled === null)) return false;
    if (n.value?.terminal === ABORTED && !a.aborted.includes(eff.op)) return true;
    return !valueFits(eff, n.value);
  });
  return bad ? fail('failure classified against the record', bad) : null;
};
S18.start = (a, item) => { a.journalIn = item.journalIn; };

// =====================================================================
// S19: a deadline sleep's length is its run's deadline; a deadline abort
// follows its completion's consumption, before the run's result. Kept: the
// deadline pairing, the consumed deadlines and run results.

const S19 = {
  mut: { issue: [...PAIRING_MUT, 'lengths'], consume: ['resultIn', 'deadlineIn'] },
  fresh: () => ({ ...pairingState(), deadlineIn: [], resultIn: [], lengths: {} }),
  event: (a, e, P) => {
    deadlinePairing(a, e, P);
    if (e.t === 'issue' && e.cmd?.c === 'sleep' && e.cmd.op === 'deadline') a.lengths[e.cmdIdx] = e.cmd.ms;
    if (e.t === 'consume') {
      const cls = classify(a, e.entry);
      if (cls.k === 'result' && ['run', 'call', 'attach'].includes(cls.c) && !a.resultIn.includes(cls.op)) a.resultIn.push(cls.op);
      if (cls.k === 'deadline') {
        const op = a.deadlineOf[e.entry.of];
        if (op !== undefined && !a.deadlineIn.some((d) => d.op === op)) a.deadlineIn.push({ op, early: !a.resultIn.includes(op) });
      }
    }
    if (e.t === 'abort' && e.cause === 'deadline') {
      const d = a.deadlineIn.find((x) => x.op === e.op);
      if (!d) hit(a, fail('deadline abort before its completion was consumed'));
      else if (!d.early) hit(a, fail('deadline abort after the run\'s result was consumed'));
    }
  },
  end: (a, item, P) => {
    const bad = Object.entries(a.deadlineOf).find(([idx, op]) =>
      journalCmd(item.journalOut, Number(idx)) && journalCmd(item.journalOut, Number(idx)).ms !== P.ops[op].deadline);
    return bad ? fail('deadline sleep length differs from the run\'s deadline', bad) : null;
  },
};

// =====================================================================
// S20: the entry gate, samples never held, entry by the signal, re-abort.
// Kept: the consumed entries not yet taken by a turn (index and kind),
// the entries watched by an entry made while they waited, whether a
// finished journal turn lacked a sample, the open turn's state (sample
// applied, action seen, an entry made after its sample and before any
// action), each sample wrapper's state, the aborts recorded, and across
// attempts each journaled abort's run and the indices consumed before it.

const S20 = {
  mut: { consume: ['consumedIdx', 'waiting', 'samples:2'], turn: ['samples:2'], sample: ['turnState'],
    deliver: ['turnState'], interrupt: ['turnState', 'lastInt'], release: ['rel'],
    abort: ['aborts', 'journaled'], wrapper: ['samples:2', 'openSampleWrappers'],
    enter: ['samples:2', 'openSampleWrappers', 'watched', 'watchedCancels', 'turnState'] },
  x0: () => ({ aborts: [] }),
  fresh: () => ({ waiting: [], watched: [], watchedCancels: [], unsampledTurn: false, turnState: null,
    samples: {}, aborts: [], journaled: [], consumedIdx: [], rel: {}, lastInt: {} }),
  start: (a, item) => { a.journalIn = item.journalIn; },
  event: (a, e, P) => {
    if (e.t === 'consume') {
      a.consumedIdx.push(e.entryIdx);
      a.waiting.push({ idx: e.entryIdx, cancel: e.entry?.e === 'cancel', early: a.rootExit === null });
      markWaited(a);
    }
    if (e.t === 'turn') turnS20(a, e);
    if (e.t === 'sample' && a.turnState) a.turnState.sampled = true;
    if ((e.t === 'deliver' || e.t === 'interrupt') && a.turnState) {
      if (a.turnState.enteredBetween !== null) hit(a, fail('closure entered before a consumed cause was acted on'));
      a.turnState.acted = true;
    }
    if (e.t === 'release' && !(e.op in a.rel)) a.rel[e.op] = e.cause;
    if (e.t === 'interrupt') a.lastInt[e.fiber] = e.cause;
    if (e.t === 'abort') abortS20(a, e, P);
    if (['wrapper', 'enter'].includes(e.t) && isSampleOp(e.op)) sampleS20(a, e);
    if (e.t === 'enter' && !isSampleOp(e.op)) enterS20(a, e);
  },
  turnEnd: (a, seg) => {
    if (seg.cause === 'journal' && seg.samples.length === 0) a.unsampledTurn = true;
  },
  end: (a, item, P, x) => endS20(a, item, x),
};

const turnS20 = (a, e) => {
  markWaited(a);
  a.turnState = e.cause === 'journal' ? { sampled: false, acted: false, enteredBetween: null } : null;
  if (e.cause !== 'journal') return;
  if (a.watched.includes(e.entryIdx)) hit(a, fail('closure entered before a consumed cause was acted on'));
  a.waiting = a.waiting.filter((w) => w.idx !== e.entryIdx);
  a.named = [...(a.named ?? []), e.entryIdx ?? null];
};

const enterS20 = (a, e) => {
  if (a.unsampledTurn) hit(a, fail('closure entered before a consumed cause was acted on'));
  const t = a.turnState;
  if (t && !t.sampled) hit(a, fail('closure entered before a consumed cause was acted on'));
  if (t && t.sampled && !t.acted) t.enteredBetween = e.pos;
  a.watched.push(...a.waiting.map((w) => w.idx));
  if (a.rootExit === null) a.watchedCancels.push(...a.waiting.filter((w) => w.cancel && w.early).map((w) => w.idx));
};

// Sample wrappers not yet entered, by command index; a consumption or a
// turn while one is open marks it as having waited.
const markWaited = (a) => (a.openSampleWrappers ?? []).forEach((idx) => { a.samples[idx].waited = true; });

const sampleS20 = (a, e) => {
  a.openSampleWrappers ??= [];
  if (e.t === 'wrapper') {
    a.samples[e.cmdIdx] = { w: e.pos, en: null, waited: false };
    a.openSampleWrappers.push(e.cmdIdx);
  } else if (a.samples[e.cmdIdx] && a.samples[e.cmdIdx].en === null) {
    a.samples[e.cmdIdx].en = e.pos;
    a.samples[e.cmdIdx].waitedBefore = a.samples[e.cmdIdx].waited;
    a.openSampleWrappers = a.openSampleWrappers.filter((idx) => idx !== e.cmdIdx);
  }
};

const abortS20 = (a, e, P) => {
  if (!a.aborts.includes(e.op)) a.aborts.push(e.op);
  const owner = P.ops[e.op]?.fiber;
  const journaled = e.cause === 'deadline' || ['race', 'exit'].includes(a.rel[e.op])
    || (e.cause === 'interrupt' && ['race', 'cancel', 'closing'].includes(a.lastInt[owner]));
  if (journaled) a.journaled.push({ op: e.op, pos: e.pos, needs: [...a.consumedIdx] });
};

const endS20 = (a, item, x) => {
  const f = sampleVerdict(a) ?? gateEnd(a) ?? signalVerdict(a, item) ?? refusedVerdict(a, item)
    ?? reAbortVerdict(a, item, x);
  x.aborts.push(...a.journaled.filter((j) => j.pos <= a.cut).map((j) => ({ op: j.op, needs: j.needs })));
  return f;
};

const sampleVerdict = (a) => {
  const bad = Object.values(a.samples).find((s) => s.w <= a.cut
    && (s.en === null || s.en > a.cut || s.waitedBefore));
  return bad ? fail('a sample waited at the gate or was held') : null;
};

const gateEnd = (a) => {
  const named = a.named ?? [];
  return a.watchedCancels.some((idx) => !named.includes(idx))
    ? fail('closure entered while a cancel signal waited') : null;
};

const signalVerdict = (a, item) => {
  const bad = item.effects.find((eff) => (eff.entered && eff.signalAbortedAtEntry)
    || (eff.entered === false && (!eff.signalAbortedAtEntry || !a.aborts.includes(eff.op))));
  return bad ? fail('closure entry against its signal', bad) : null;
};

const refusedVerdict = (a, item) => {
  if (!PERSISTED.includes(item.end.kind)) return null;
  const bad = item.effects.find((eff) => eff.entered === false
    && runResult(item.journalOut, eff.op)?.value?.terminal !== ABORTED);
  return bad ? fail('refused run\'s terminal abort not journaled', bad) : null;
};

const reAbortVerdict = (a, item, x) => {
  const inIdx = a.journalIn.map((e) => e.idx);
  const bad = x.aborts.find((ab) => ab.needs.every((i) => inIdx.includes(i)) && !runResult(a.journalIn, ab.op)
    && item.effects.some((e) => e.op === ab.op && e.entered));
  return bad ? fail('closure re-entered although the journal holds its abort', bad) : null;
};

// =====================================================================
// S21: the final outcome by precedence. Kept: whether a violation occurred
// (and its first position), the root's exit outcome and position, whether
// the root's cancel interrupt preceded its exit, and the last attempt's
// end kind with the outcome it requires.

const S21 = {
  x0: () => ({ last: null }),
  fresh: () => ({ exit: null, rootCancelBeforeExit: false }),
  event: (a, e, P) => {
    if (e.t === 'rootExit' && a.exit === null) a.exit = e.outcome;
    if (e.t === 'interrupt' && e.fiber === P.root && e.cause === 'cancel' && a.rootExit === null) a.rootCancelBeforeExit = true;
  },
  end: (a, item, P, x) => {
    const out = item.journalOut.find((e) => e.e === 'output');
    const want = a.viol !== null && a.viol <= a.cut ? 'defect' : !a.exit ? null
      : a.exit.kind === 'defect' ? 'defect' : a.rootCancelBeforeExit ? 'cancelled' : a.exit.kind;
    x.last = { kind: item.end.kind, want: item.end.kind === 'output' ? want : null };
    if (item.end.kind === 'retry') return out ? fail('a retried attempt wrote output') : null;
    if (item.end.kind !== 'output') return null;
    if (!want) return fail('output with no root exit and no violation');
    return out && out.outcome.kind !== want ? fail('output outcome breaks precedence', { want }) : null;
  },
  final: (x, item) => {
    if (x.last?.kind === 'retry') return item.outcome ? fail('retried attempt decided a final outcome') : null;
    return x.last?.kind === 'output' && item.outcome?.kind !== x.last.want
      ? fail('final outcome breaks precedence') : null;
  },
};

// =====================================================================
// S22: what each cut does. Kept: the event count, the aborts recorded and
// the first "ended" abort's position, the issues (index, position) to judge
// against the cut, and across attempts the cancel targets and kills.

const S22 = {
  mut: { abort: ['aborts'], issue: ['iss'] },
  x0: () => ({ targets: [], killed: false }),
  fresh: () => ({ aborts: [], endedAt: null, iss: [] }),
  event: (a, e) => {
    if (e.t === 'abort') {
      if (!a.aborts.includes(e.op)) a.aborts.push(e.op);
      if (e.cause === 'ended') a.endedAt ??= e.pos;
    }
    if (e.t === 'issue') a.iss.push({ pos: e.pos, idx: e.cmdIdx });
  },
  end: (a, item, P, x) => {
    const journal = item.journalOut;
    x.targets.push(...journal.filter((e) => e.e === 'cmd' && e.cmd.c === 'cancelCall').map((e) => e.cmd.target));
    if (item.end.kind === 'killed') x.killed = true;
    if (['crashed', 'killed'].includes(item.end.kind) && a.pos - 1 > a.cut) return fail('events after a crash or kill');
    if (item.end.kind === 'ended' && item.effects.some((e) => e.entered && e.settled === null && !a.aborts.includes(e.op))) {
      return fail('run executing at an Ended cut was not aborted');
    }
    if (a.iss.some((i) => i.pos > a.cut && journal.some((e) => e.idx === i.idx))) {
      return fail('command issued after the cut reached the journal');
    }
    return a.endedAt !== null && !(item.end.kind === 'ended' && a.endedAt > a.cut)
      ? fail('ended abort outside an Ended cut') : null;
  },
  final: (x, item) => {
    const bad = (item.children ?? []).find((c) => (c.cancelled && !x.targets.includes(c.viaCmd))
      || (c.killed && !x.killed));
    return bad ? fail('child cancelled or killed by a cut', bad) : null;
  },
};

// =====================================================================
// S23: exit, closing and finalizers. Kept: for each operation issued its
// owner and whether it is still pending (not delivered, released or
// completed); the live fibers at the root's exit and those interrupted for
// closing after it; the calls released after the exit; retained runs; the
// consumed entries' positions; the refused start; the root's cancellation;
// and the non-cancel issues to judge against closing and the cut.

const S23 = {
  mut: { issue: ['pending', 'ids', 'compIdx', 'others'], deliver: ['pending'],
    consume: ['cons', 'pending', 'resultIn'], release: ['released', 'pending', 'retained', 'owedCalls'],
    interrupt: ['closed'] },
  fresh: () => ({ pending: {}, live: null, closed: [], owedCalls: [], retained: [], cons: {},
    refusedAt: null, rootCancelled: false, others: [], resultIn: [], ids: {}, released: [], compIdx: [] }),
  event: (a, e, P) => {
    if (e.t === 'issue') {
      if (P.ops[e.cmd?.op] && ['run', 'sleep', 'call', 'send', 'attach'].includes(e.cmd.c)) a.pending[e.cmd.op] ??= true;
      if (['call', 'send'].includes(e.cmd?.c)) a.ids[e.cmd.op] ??= e.cmdIdx;
      if (e.cmd?.c === 'send' && a.rootCancelled && !P.daemon[P.ops[e.cmd.op]?.fiber]) a.compIdx.push(e.cmdIdx);
      if (!(e.cmd?.c === 'cancelCall' && e.cmd.by === 'executor')) a.others.push({ pos: e.pos, idx: e.cmdIdx, closing: e.pos >= closing(a) });
    }
    if (e.t === 'deliver') a.pending[e.op] = false;
    if (e.t === 'consume') {
      a.cons[e.entryIdx] ??= e.pos;
      const cls = classify(a, e.entry);
      if (cls.k === 'result' && ['run', 'call', 'attach'].includes(cls.c)) {
        a.pending[cls.op] = false;
        if (!a.resultIn.includes(cls.op)) a.resultIn.push(cls.op);
      }
    }
    if (e.t === 'release') releaseS23(a, e, P);
    if (e.t === 'rootExit' && a.live === null) {
      a.live = [...new Set(Object.entries(a.pending).filter(([, p]) => p).map(([op]) => P.ops[op].fiber))]
        .filter((f) => f !== P.root);
    }
    if (e.t === 'interrupt' && e.cause === 'closing' && a.rootExit !== null && e.pos > a.rootExit) a.closed.push(e.fiber);
    if (e.t === 'interrupt' && e.fiber === P.root && e.cause === 'cancel' && a.rootExit === null) a.rootCancelled = true;
    if (e.t === 'violation' && e.kind === 'refusedAtClosing' && a.refusedAt === null) {
      a.refusedAt = e.pos;
      if (a.rootExit === null && a.viol === e.pos) hit(a, fail('start refused before closing'));
    }
  },
  end: (a, item, P) => endS23(a, item, P),
};

// The first release of an operation: a run not yet completed is retained;
// a call released after the root's exit and not completed must be
// cancelled before Output.
const releaseS23 = (a, e, P) => {
  if (a.released.includes(e.op)) return;
  a.released.push(e.op);
  if (a.pending[e.op] !== undefined) a.pending[e.op] = false;
  const open = !a.resultIn.includes(e.op);
  if (P.ops[e.op]?.s === 'run' && open) a.retained.push(e.op);
  if (P.ops[e.op]?.s === 'call' && open && a.rootExit !== null && e.pos > a.rootExit) a.owedCalls.push(e.op);
};

const endS23 = (a, item, P) => {
  const journal = item.journalOut;
  const bad = a.others.find((o) => (o.closing || o.pos > a.cut) && journalCmd(journal, o.idx)
    && !(journalCmd(journal, o.idx).c === 'cancelCall' && journalCmd(journal, o.idx).by === 'executor'));
  if (bad) return fail('command issued after closing latched', bad);
  const out = journal.find((e) => e.e === 'output');
  const outIdx = out?.idx ?? Infinity;
  if (item.end.kind === 'output' && a.rootExit !== null) {
    const f = exitWait(a, item, P, outIdx);
    if (f) return f;
  }
  if (a.refusedAt !== null && out && out.outcome.kind !== 'defect') return fail('refused start did not make the outcome a defect');
  if (out && a.rootCancelled && a.rootExit !== null) {
    const want = a.viol !== null && a.viol <= a.cut ? 'defect' : 'cancelled';
    if (out.outcome.kind !== want) return fail('exit after a cancellation reported the wrong outcome');
  }
  return null;
};

const consumedBy = (a, idx) => idx in a.cons && a.cons[idx] <= a.cut;

const exitWait = (a, item, P, outIdx) => {
  const journal = item.journalOut;
  const left = (a.live ?? []).find((f) => !a.closed.includes(f));
  if (left) return fail('live fiber not interrupted at exit', { fiber: left });
  const eff = item.effects.find((e) => (e.entered && e.settled === null)
    || (e.settled !== 'retryable' && e.entered !== null
      && !(runResult(journal, e.op)?.idx < outIdx && consumedBy(a, runResult(journal, e.op).idx))));
  if (eff) return fail('output before a closure settled or was acknowledged', eff);
  const ret = a.retained.find((op) => !(runResult(journal, op)?.idx < outIdx && consumedBy(a, runResult(journal, op).idx)));
  if (ret) return fail('output before a retained run\'s result was consumed', { op: ret });
  const comps = a.compIdx;
  const call = a.owedCalls.find((op) => {
    const idx = a.ids[op];
    if (idx === undefined || comps.includes(idx)) return false;
    const c = journal.find((e) => e.e === 'cmd' && e.cmd.c === 'cancelCall' && e.cmd.by === 'executor'
      && e.cmd.target === idx && e.idx < outIdx);
    const id = journal.find((e) => e.e === 'notif' && e.of === idx && isId(e.value));
    return !(c && id && consumedBy(a, id.idx));
  });
  return call ? fail('output before a closing cancel was issued', { op: call }) : null;
};

// =====================================================================
// S25, S26: warnings. Kept: the aborted runs, the runs whose result was
// consumed, and each warning's runs with the aborted and consumed sets at
// its time; judged with the effects at attemptEnd.

const warnClaim = (which) => ({
  mut: { abort: ['aborted'], consume: ['done'], warn: ['warns'] },
  fresh: () => ({ aborted: [], done: [], warns: [] }),
  event: (a, e) => {
    if (e.t === 'abort' && !a.aborted.includes(e.op)) a.aborted.push(e.op);
    if (e.t === 'consume') {
      const cls = classify(a, e.entry);
      if (cls.k === 'result' && ['run', 'call', 'attach'].includes(cls.c) && !a.done.includes(cls.op)) a.done.push(cls.op);
    }
    if (e.t === 'warn' && e.which === which) a.warns.push({ runs: e.runs, aborted: [...a.aborted], done: [...a.done] });
  },
  end: (a, item) => {
    const entered = item.effects.filter((e) => e.entered).map((e) => e.op);
    const named = (w) => w.runs.find((op) => !w.aborted.includes(op) || !entered.includes(op) || w.done.includes(op));
    if (which === 1) {
      if (a.warns.length > 1) return fail('first warning emitted twice');
      const [w] = a.warns;
      if (!w) return null;
      if (!w.runs.length) return fail('first warning names no run');
      const holding = item.effects.filter((e) => e.entered && e.settled === null && w.aborted.includes(e.op));
      if (holding.some((e) => !w.runs.includes(e.op))) return fail('first warning omits an aborted run holding the attempt');
      return named(w) ? fail('warning names a run it may not name') : null;
    }
    const all = a.warns.flatMap((w) => w.runs);
    if (all.some((op, k) => all.indexOf(op) !== k)) return fail('second warning emitted twice for a run');
    return a.warns.some(named) ? fail('warning names a run it may not name') : null;
  },
});

// =====================================================================

/** One online monitor per predicate, with the predicate's id. */
export const monitors = [
  monitor('S1', S1), monitor('S2', S2), monitor('S3', S3), monitor('S4', S4),
  monitor('S6', S6), monitor('S7', S7), P2, P3, P4, P5, P6, P7, P8,
  monitor('S10', S10), monitor('S11', S11), monitor('S12', S12), monitor('S13', S13),
  monitor('S14a', S14a), monitor('S14b', S14b), monitor('S14d', S14d), monitor('S15', S15),
  monitor('S16a', S16a), monitor('S16b', S16b), monitor('S16c', S16c), monitor('S16d', S16d),
  monitor('S16e', S16e), monitor('S16f', S16f), monitor('S17', S17), monitor('S18', S18),
  monitor('S19', S19), monitor('S20', S20), monitor('S21', S21), monitor('S22', S22),
  monitor('S23', S23), monitor('S25', warnClaim(1)), monitor('S26', warnClaim(2)),
];
