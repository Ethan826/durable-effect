// Predicates for the step 7 bounded exhaustive check of design revision 6
// (issue #48: part 2, comment 7142429247, is the specification; comment
// 7144185705 says which statements are checked). Each predicate is written
// from its statement's text and reads only a history in the format fixed by
// HISTORY.md. It shares no code with the environment or executor models.
//
// A predicate's check returns null when the history satisfies the claim, or
// { msg, detail } with a concrete witness when it does not.
//
// Reading conventions, chosen from the statements' text and HISTORY.md:
// - A trace position belongs to its attempt when it is at most end.at.
// - Closing starts at the root's exit or at the first violation, whichever is
//   first (#37 X6). "While the attempt is open" means before that point.
// - A turn segment runs from a `turn` event to the next one. The turn's
//   events (its sample, its delivery, the fibers it runs) lie inside it.
// - An operation is released at its first `release` event (a fiber stopped
//   awaiting or owning it). A journal turn's cause is the entry its
//   `entryIdx` names.
// - A turn is complete once it has run past its sample inside the attempt:
//   another event of the attempt follows the sample in the same turn, or the
//   next turn has started. A turn the attempt's end cuts short owes nothing.
// - An effect with `entered: null` was held by the wrapper when the attempt
//   ended: neither an execution nor a refusal.
// - A compensation is a send issued after the root's cancellation interrupt
//   by a fiber that is not a daemon (§6: "finalizers and compensations in the
//   root's scope").

// ---------------------------------------------------------------- generic

const fail = (msg, detail = {}) => ({ msg, detail });

const firstFailure = (items, check) => {
  for (const item of items) {
    const result = check(item);
    if (result) return result;
  }
  return null;
};

const checks = (...thunks) => firstFailure(thunks, (thunk) => thunk());

const canon = (value) => {
  if (Array.isArray(value)) return value.map(canon);
  if (value && typeof value === 'object') {
    const keys = Object.keys(value).sort();
    return Object.fromEntries(keys.map((key) => [key, canon(value[key])]));
  }
  return value;
};

const same = (a, b) => JSON.stringify(canon(a)) === JSON.stringify(canon(b));

const isPrefix = (short, long) =>
  short.length <= long.length && short.every((x, i) => same(x, long[i]));

const minPos = (positions) => Math.min(Infinity, ...positions);

const DURABLE = new Set(['run', 'sleep', 'call', 'send', 'attach']);
const RESULT_CMDS = new Set(['run', 'call', 'attach']);
const isIdValue = (value) =>
  !!value && typeof value === 'object' && 'invocationId' in value;
const ABORTED = 'aborted';

// ---------------------------------------------------------------- program

const programCache = new WeakMap();

const indexProgram = (program) => {
  if (programCache.has(program)) return programCache.get(program);
  const ops = new Map();
  const races = [];
  const visit = (fiber, region) => (stmt) => {
    if (['run', 'sleep', 'call'].includes(stmt.s)) {
      ops.set(stmt.op, { op: stmt.op, fiber, stmt, ...region, partner: null });
    } else if (stmt.s === 'race') {
      races.push(stmt.ops);
    } else if (stmt.s === 'uninterruptible') {
      stmt.body.forEach(visit(fiber, { ...region, protected: true }));
    } else if (stmt.s === 'ensuring') {
      stmt.body.forEach(visit(fiber, region));
      const fin = { ...region, protected: true, finalizer: true };
      stmt.finalizer.forEach(visit(fiber, fin));
    }
  };
  const plain = { protected: false, finalizer: false };
  program.fibers.forEach((f) => f.body.forEach(visit(f.id, plain)));
  races.forEach(([a, b]) => {
    if (ops.has(a)) ops.get(a).partner = b;
    if (ops.has(b)) ops.get(b).partner = a;
  });
  const daemon = new Map(program.fibers.map((f) => [f.id, !!f.daemon]));
  const indexed = { ops, daemon, root: program.fibers[0]?.id ?? 'f0' };
  programCache.set(program, indexed);
  return indexed;
};

// ---------------------------------------------------------------- attempt

const attemptCache = new WeakMap();

const classify = (cmdOf, entry) => {
  if (!entry) return { kind: 'missing' };
  if (entry.e === 'cancel') return { kind: 'cancel' };
  if (entry.e !== 'notif') return { kind: entry.e };
  const cmd = cmdOf(entry.of);
  if (!cmd) return { kind: 'orphan' };
  if (isIdValue(entry.value)) return { kind: 'id', cmd };
  if (cmd.c === 'run' && cmd.op === 'sample') return { kind: 'sample', cmd };
  if (cmd.c === 'sleep' && cmd.op === 'deadline') {
    return { kind: 'deadline', cmd };
  }
  return { kind: 'result', cmd, op: cmd.op };
};

// Each delivery is matched to its turn's cause when that cause is a result
// of the delivered operation, else to the latest consumed result of the
// operation that no earlier delivery took.
const mapDeliveries = (events, consumes, segments) => {
  const used = new Set();
  const turnCause = (d) => {
    const seg = segments.find((s) => s.start <= d.pos && d.pos < s.end);
    const c = seg?.cause === 'journal'
      && consumes.find((x) => x.idx === seg.entryIdx && x.pos < d.pos);
    return c && c.cls.kind === 'result' && c.cls.op === d.op ? c : null;
  };
  const matchOne = (d) => {
    const found = turnCause(d) ?? [...consumes].reverse().find((c) =>
      c.pos < d.pos && c.cls.kind === 'result' && c.cls.op === d.op
      && !used.has(c.idx));
    if (found) used.add(found.idx);
    return { ...d, notif: found ?? null };
  };
  return events.filter((e) => e.t === 'deliver').map(matchOne);
};

const firstByKey = (items, key, value) => {
  const map = new Map();
  items.forEach((x) => { if (!map.has(key(x))) map.set(key(x), value(x)); });
  return map;
};


// The format does not say which run a deadline sleep belongs to (see
// missingFields). A deadline sleep is paired with the nearest earlier run
// command whose statement declares a deadline, else the nearest later one.
const pairDeadlines = (prog, journal) => {
  const cmds = journal.filter((e) => e.e === 'cmd')
    .sort((a, b) => a.idx - b.idx);
  const hasDeadline = (e) => e.cmd.c === 'run'
    && prog.ops.get(e.cmd.op)?.stmt.deadline !== undefined;
  const runs = cmds.filter(hasDeadline);
  const taken = new Set();
  const byDeadline = new Map();
  const pickRun = (d) => {
    const free = runs.filter((r) => !taken.has(r.cmd.op));
    return free.filter((r) => r.idx < d.idx).at(-1)
      ?? free.find((r) => r.idx > d.idx);
  };
  cmds.filter((e) => e.cmd.c === 'sleep' && e.cmd.op === 'deadline')
    .forEach((d) => {
      const run = pickRun(d);
      if (run) { taken.add(run.cmd.op); byDeadline.set(d.idx, run.cmd.op); }
    });
  return byDeadline;
};

const buildIndex = (history, att) => {
  const prog = indexProgram(history.program);
  const jmap = new Map(att.journalOut.map((e) => [e.idx, e]));
  const cmdOf = (idx) => (jmap.get(idx)?.e === 'cmd' ? jmap.get(idx).cmd : null);
  const ev = att.trace.map((event, pos) => ({ ...event, pos }));
  const ofType = (t) => ev.filter((e) => e.t === t);
  const firstPos = (t) => ev.find((e) => e.t === t)?.pos ?? Infinity;
  const consumes = ofType('consume').map((e) => {
    const entry = jmap.get(e.entryIdx) ?? null;
    return { pos: e.pos, idx: e.entryIdx, entry, cls: classify(cmdOf, entry) };
  });
  const issues = ofType('issue').map((e) =>
    ({ pos: e.pos, fiber: e.fiber, cmdIdx: e.cmdIdx, cmd: cmdOf(e.cmdIdx) }));
  const turns = ofType('turn');
  const segments = turns.map((t, k) => ({ k, start: t.pos,
    end: turns[k + 1]?.pos ?? ev.length, cause: t.cause, entryIdx: t.entryIdx }));
  const delivers = mapDeliveries(ev, consumes, segments);
  const releaseEvents = ofType('release');
  const deliveredAt = firstByKey(delivers, (d) => d.op, (d) => d.pos);
  const interrupts = ofType('interrupt');
  const rootExit = firstPos('rootExit');
  const firstViolation = firstPos('violation');
  return {
    att, prog, jmap, cmdOf, ev, consumes, issues, segments, delivers,
    deliveredAt, interrupts, rootExit, firstViolation,
    cut: att.end.at,
    freeze: firstPos('freeze'),
    closing: Math.min(rootExit, firstViolation),
    samples: ofType('sample'),
    clocks: ofType('clock'),
    aborts: ofType('abort'),
    warns: ofType('warn'),
    violations: ofType('violation'),
    releases: firstByKey(releaseEvents, (r) => r.op, (r) => r.pos),
    releaseCause: firstByKey(releaseEvents, (r) => r.op, (r) => r.cause),
    deadlineRun: pairDeadlines(prog, att.journalOut),
  };
};

const ix = (history, att) => {
  if (!attemptCache.has(att)) attemptCache.set(att, buildIndex(history, att));
  return attemptCache.get(att);
};

// A predicate is a specification folded over the attempts in order:
// - attempt(I): judges one attempt alone;
// - summarize(I): what later attempts or the end need from this attempt;
// - across(summaries, current): judges the new attempt against earlier ones;
// - keep(current): the part of the summary kept for later (default: all);
// - final(summaries, { outcome, children }): judges the whole invocation;
// - trace: false when no part reads trace events.
// The same fold drives the history-level check here and the stream monitors
// in monitors.mjs.
const perAttempt = (check) => ({ attempt: check });

const tagged = (r, n) => r && fail(r.msg, { attempt: n, ...r.detail });

const foldAttempt = (spec, sums, I) => {
  const r = spec.attempt ? spec.attempt(I) : null;
  if (r) return { verdict: tagged(r, I.att.n), sums };
  if (!spec.summarize) return { verdict: null, sums };
  const cur = spec.summarize(I);
  const x = spec.across ? spec.across(sums, cur) : null;
  const kept = spec.keep ? spec.keep(cur) : cur;
  return { verdict: tagged(x, I.att.n), sums: [...sums, kept] };
};

const runSpec = (spec) => (history) => {
  let sums = [];
  for (const att of history.attempts) {
    const step = foldAttempt(spec, sums, ix(history, att));
    if (step.verdict) return step.verdict;
    sums = step.sums;
  }
  return spec.final ? spec.final(sums, history) : null;
};

// ------------------------------------------------------- attempt queries

const segmentAt = (I, pos) =>
  I.segments.find((s) => s.start <= pos && pos < s.end) ?? null;

const inSegment = (seg, list) =>
  list.filter((e) => e.pos >= seg.start && e.pos < seg.end);

const issuePosOf = (I, cmdIdx) =>
  I.issues.find((i) => i.cmdIdx === cmdIdx)?.pos ?? Infinity;

const consumePosOf = (I, idx) =>
  I.consumes.find((c) => c.idx === idx)?.pos ?? Infinity;

const resultConsumePos = (I, op) => minPos(I.consumes
  .filter((c) => c.cls.kind === 'result' && c.cls.op === op
    && RESULT_CMDS.has(c.cls.cmd.c))
  .map((c) => c.pos));

const idConsumePos = (I, cmdIdx) => minPos(I.consumes
  .filter((c) => c.cls.kind === 'id' && c.entry.of === cmdIdx)
  .map((c) => c.pos));

const opIssue = (I, op, kinds = DURABLE) =>
  I.issues.find((i) => i.cmd?.op === op && kinds.has(i.cmd.c)) ?? null;

const cmdEntries = (journal) => journal.filter((e) => e.e === 'cmd');

const runResultIn = (journal, op) => {
  const runIdx = new Set(cmdEntries(journal)
    .filter((e) => e.cmd.c === 'run' && e.cmd.op === op).map((e) => e.idx));
  return journal.find((e) => e.e === 'notif' && runIdx.has(e.of)
    && !isIdValue(e.value)) ?? null;
};

const outputEntry = (journal) => journal.find((e) => e.e === 'output') ?? null;

const rootCancelPos = (I) => I.interrupts
  .find((x) => x.fiber === I.prog.root && x.cause === 'cancel')?.pos
  ?? Infinity;

const executorCancels = (I) => I.issues
  .filter((i) => i.cmd?.c === 'cancelCall' && i.cmd.by === 'executor');

const compensations = (I) => {
  const after = rootCancelPos(I);
  const isComp = (i) => i.cmd?.c === 'send' && i.pos > after
    && !I.prog.daemon.get(I.prog.ops.get(i.cmd.op)?.fiber);
  return new Set(I.issues.filter(isComp).map((i) => i.cmdIdx));
};

const effectsOf = (att) => att.effects ?? [];

const nextConsumeAfter = (I, pos) =>
  I.consumes.find((c) => c.pos > pos)?.pos ?? Infinity;

// ----------------------------------------------------- turns and causes

const journalSegments = (I) => I.segments.filter((s) => s.cause === 'journal');

// Each journal turn with the consumed entry its entryIdx names, if the race
// consumed that entry before the turn began.
const matchTurns = (I) => journalSegments(I).map((seg) => ({
  seg,
  cause: I.consumes.find((c) => c.idx === seg.entryIdx && c.pos < seg.start) ?? null,
}));

// Causes: cancel signals consumed before the root's exit and the freeze, and
// entries some journal turn names.
const causeEntries = (I) => {
  const named = new Set(journalSegments(I).map((s) => s.entryIdx));
  const limit = Math.min(I.freeze, I.rootExit);
  return I.consumes.filter((c) => (c.cls.kind === 'cancel' && c.pos < limit)
    || named.has(c.idx));
};

// A turn is complete once it has run past its sample inside the attempt.
const turnCompleted = (I, seg) => {
  if (seg.end <= I.cut) return true;
  const s = inSegment(seg, I.samples)[0];
  const next = s && I.ev[s.pos + 1];
  return !!next && next.pos < seg.end && next.pos <= I.cut
    && !['freeze', 'warn'].includes(next.t);
};

// --------------------------------------------------- trace comparison

// The trace as S1 compares it is what handler code can observe (#37):
// commands issued, deliveries, interruptions, clock reads, draws, violations
// and the root's exit. It runs up to the attempt's end, or the freeze if
// earlier (part 2, "Kept from #37": the freeze is an end for comparison).
// Left out: the closure lifecycle (`wrapper`, `enter`, `refuse`, `done`,
// `settle`, `propose`), which differs legitimately on replay because a run
// whose result is journaled is never asked for again; `freeze`, `warn`,
// `abort`, `release`, `turn` and `sample`, which handler code does not see.
// Of the events left out, two still matter to the comparison: `consume`
// gives the inputs, which decide how far two attempts must agree, and the
// freeze bounds the compared trace. S2's command comparison reads the
// command of each observable `issue` from the journal.
const OBSERVABLE = new Set(['issue', 'deliver', 'interrupt', 'clock', 'draw',
  'violation', 'rootExit']);

const observed = (e) => {
  if (e.t === 'issue') return { t: 'issue', fiber: e.fiber, cmdIdx: e.cmdIdx };
  const { pos, ...rest } = e;
  return rest;
};

// An attempt's projection: its inputs (consumed entries, in order), its
// observable events, each with the number of inputs consumed before it, and
// the journaled command of each issue. It is all S1, S2 (pairs), S3 and S10
// need.
const attemptProjection = (I) => {
  const inputs = [];
  const obs = [];
  const cmds = {};
  I.ev.slice(0, Math.min(I.cut + 1, I.freeze)).forEach((e) => {
    if (e.t === 'consume') inputs.push(I.jmap.get(e.entryIdx) ?? { missing: e.entryIdx });
    if (!OBSERVABLE.has(e.t)) return;
    obs.push({ ...observed(e), seen: inputs.length });
    const cmd = e.t === 'issue' ? I.cmdOf(e.cmdIdx) : null;
    if (cmd) cmds[e.cmdIdx] = cmd;
  });
  return { inputs, obs, cmds };
};

// "Same inputs up to a point" (#37 X1, kept by part 1 §1): the two attempts
// consumed the same exogenous entries (each consumed notification's value
// and where each cancel signal falls), in the same order, up to that point,
// from the same program and seed (the invocation id). With k the length of
// the common prefix of the two input sequences, each attempt's comparable
// trace is its observable events seen after at most k inputs. If both went
// on to consume a different (k+1)-th input, both traces reached that point
// and must be equal; otherwise one attempt stopped (its cut), and its trace
// must be a prefix of the other's.
const comparable = (A, B) => {
  let k = 0;
  while (k < A.inputs.length && k < B.inputs.length && same(A.inputs[k], B.inputs[k])) k += 1;
  const diverged = k < A.inputs.length && k < B.inputs.length;
  const upTo = (P) => P.obs.filter((e) => e.seen <= k).map(({ seen, ...e }) => e);
  return { a: upTo(A), b: upTo(B), diverged };
};

const compareProjections = (A, B, withCommands) => {
  const { a: pa, b: pb, diverged } = comparable(A, B);
  for (let i = 0; i < Math.min(pa.length, pb.length); i += 1) {
    const [a, b] = [pa[i], pb[i]];
    if (!same(a, b)) return fail('traces differ before the common cut', { i, a, b });
    if (withCommands && a.t === 'issue') {
      const [ca, cb] = [A.cmds[a.cmdIdx], B.cmds[b.cmdIdx]];
      if (ca && cb && !same(ca, cb)) {
        return fail('same inputs, different command', { i, a: ca, b: cb });
      }
    }
  }
  return diverged && pa.length !== pb.length
    ? fail('traces differ before the common cut', { lengths: [pa.length, pb.length] })
    : null;
};

const drawsByFiber = (events) => {
  const map = new Map();
  events.filter((e) => e.t === 'draw').forEach((e) =>
    map.set(e.fiber, [...(map.get(e.fiber) ?? []), e.value]));
  return map;
};

const compareDraws = (A, B) => {
  const { a, b, diverged } = comparable(A, B);
  const [da, db] = [drawsByFiber(a), drawsByFiber(b)];
  const fibers = new Set([...da.keys(), ...db.keys()]);
  return firstFailure([...fibers], (f) => {
    const [xa, xb] = [da.get(f) ?? [], db.get(f) ?? []];
    const agree = diverged ? same(xa, xb)
      : isPrefix(xa, xb) || isPrefix(xb, xa);
    return agree ? null : fail('draws differ', { fiber: f, a: xa, b: xb });
  });
};

const compareViolations = (A, B) => {
  const { a, b } = comparable(A, B);
  const reach = Math.min(a.length, b.length);
  const at = (p) => p.slice(0, reach).flatMap((e, i) =>
    (e.t === 'violation' ? [{ i, kind: e.kind }] : []));
  return same(at(a), at(b)) ? null
    : fail('violations at different positions', { a: at(a), b: at(b) });
};

// Each attempt keeps its projection; a new attempt is compared with all
// earlier ones.
const acrossAttempts = (compare) => ({
  summarize: (I) => ({ n: I.att.n, proj: attemptProjection(I) }),
  across: (sums, cur) => firstFailure(sums, (s) => {
    const r = compare(s.proj, cur.proj);
    return r && fail(r.msg, { attempts: [s.n, cur.n], ...r.detail });
  }),
});

// ------------------------------------------------------------- S1, S2

const S1 = acrossAttempts((A, B) => compareProjections(A, B, true));

const executorCmdIdx = (journal) => cmdEntries(journal)
  .filter((e) => !(e.cmd.c === 'cancelCall' && e.cmd.by === 'sdk'))
  .map((e) => e.idx);

const journalInIsPrefix = (I) => (isPrefix(I.att.journalIn, I.att.journalOut)
  ? null : fail('journalIn is not a prefix of journalOut'));

// Every persisted command is issued in journal order: the issued commands
// that reached the journal are a prefix of its executor commands, and every
// command new in this attempt was issued by it.
const issuedInJournalOrder = (I) => {
  const issued = I.issues.filter((i) => i.pos <= I.cut);
  const notCmd = issued.find((i) => I.jmap.has(i.cmdIdx) && !i.cmd);
  if (notCmd) return fail('issue names a journal entry that is no command', notCmd);
  const persisted = issued.filter((i) => i.cmd).map((i) => i.cmdIdx);
  const all = executorCmdIdx(I.att.journalOut);
  const inSet = new Set(I.att.journalIn.map((e) => e.idx));
  const fresh = all.filter((idx) => !inSet.has(idx));
  if (!isPrefix(persisted, all)) {
    return fail('issued commands are not the journal commands in order',
      { issued: persisted, journal: all });
  }
  const missing = fresh.find((idx) => !persisted.includes(idx));
  return missing === undefined ? null
    : fail('journal command not issued by this attempt', { cmdIdx: missing });
};

const issuerOwnsOp = (I) => firstFailure(I.issues, (i) => {
  const owner = I.prog.ops.get(i.cmd?.op)?.fiber;
  const own = ['run', 'sleep', 'call', 'send'].includes(i.cmd?.c);
  return own && owner && i.fiber !== owner
    ? fail('command issued by a fiber that does not own it', i) : null;
});

const issueList = (I) => I.issues.map((i) => ({ cmdIdx: i.cmdIdx, fiber: i.fiber, cmd: i.cmd }));

const firstIssues = (issues) => {
  const first = {};
  issues.forEach((i) => { if (!(i.cmdIdx in first)) first[i.cmdIdx] = i; });
  return first;
};

const sameIssuerOnReplay = (first, issues) => firstFailure(issues, (ib) => {
  const ia = first[ib.cmdIdx];
  const both = ia && ia.cmd && ib.cmd && same(ia.cmd, ib.cmd);
  return both && ia.fiber !== ib.fiber
    ? fail('replay issues a journal command from another fiber', { ia, ib })
    : null;
});

// A replay over a common journal prefix has the same inputs there, so a
// journal mismatch is always a command that differs from the journal's.
const noMismatch = (I) => (I.att.end.detail === 'mismatch'
  ? fail('replay issued a command different from the journal\'s') : null);

// Kept per attempt: the first issue of each journal index (issuer and
// command), for the issuer check on later replays.
const S2 = {
  attempt: (I) => checks(
    () => noMismatch(I),
    () => journalInIsPrefix(I),
    () => issuedInJournalOrder(I),
    () => issuerOwnsOp(I)),
  summarize: (I) => ({ issues: issueList(I) }),
  across: (sums, cur) => firstFailure(sums, (s) => sameIssuerOnReplay(s.first, cur.issues)),
  keep: (cur) => ({ first: firstIssues(cur.issues) }),
};

const S3 = acrossAttempts(compareViolations);
const S10 = acrossAttempts(compareDraws);

// ------------------------------------------------------------------ S4

const oneDeliveryPerTurn = (I) => firstFailure(I.segments, (seg) => {
  const ds = inSegment(seg, I.delivers).filter((d) => d.pos < I.closing);
  return ds.length > 1
    ? fail('two results delivered in one turn', { turn: seg.start, ds }) : null;
});

const consumedOnce = (I) => {
  const seen = new Set();
  return firstFailure(I.consumes, (c) => {
    if (seen.has(c.idx)) return fail('entry consumed twice', c);
    seen.add(c.idx);
    return null;
  });
};

const cancelledBefore = (I, cmdIdx, pos) => executorCancels(I)
  .some((x) => x.cmd.target === cmdIdx && x.pos < pos);

const consumedNonMember = (I, c) => {
  if (c.cls.kind === 'deadline') {
    const run = I.deadlineRun.get(c.entry.of);
    return run !== undefined && resultConsumePos(I, run) < c.pos;
  }
  if (c.cls.kind !== 'result' || c.cls.cmd.c === 'run') return false;
  return (I.releases.get(c.cls.op) ?? Infinity) < c.pos
    || cancelledBefore(I, c.entry.of, c.pos);
};

const noNonMemberConsumed = (I) => firstFailure(
  I.consumes.filter((c) => c.pos <= I.cut),
  (c) => (consumedNonMember(I, c)
    ? fail('race consumed a result of an operation in no set', c) : null));

// Members whose presence in the race the statement fixes, whatever the
// fibers do: every run (samples included) until its result is consumed,
// every invocation-id promise, every deadline sleep whose run's result has
// not been consumed, and operations awaited by fibers while nothing has been
// interrupted, nothing raced and the root has not exited.
const definiteMember = (I, entry, pos) => {
  const cls = classify(I.cmdOf, entry);
  if (!(issuePosOf(I, entry.of) < pos)) return false;
  if (cls.kind === 'id' || cls.kind === 'sample') return true;
  if (cls.kind === 'deadline') {
    const run = I.deadlineRun.get(entry.of);
    const runNotif = run && runResultIn(I.att.journalOut, run);
    return run !== undefined && !(resultConsumePos(I, run) < pos)
      && !(runNotif && runNotif.idx < entry.idx);
  }
  if (cls.kind !== 'result') return false;
  if (cls.cmd.c === 'run') return true;
  return I.rootExit > pos && !(I.deliveredAt.get(cls.op) < pos)
    && !(I.releases.get(cls.op) < pos)
    && !cancelledBefore(I, entry.of, pos);
};

const skippedMember = (I, c) => {
  const consumedBefore = new Set(I.consumes
    .filter((x) => x.pos < c.pos).map((x) => x.idx));
  return I.att.journalOut.find((e) => e.e === 'notif' && e.idx < c.idx
    && !consumedBefore.has(e.idx) && definiteMember(I, e, c.pos)) ?? null;
};

const membersNotSkipped = (I) => firstFailure(
  I.consumes.filter((c) => c.pos <= I.cut), (c) => {
    const skipped = skippedMember(I, c);
    return skipped
      ? fail('race consumed an entry past a member it skipped', { c, skipped })
      : null;
  });

const S4 = perAttempt((I) => checks(
  () => oneDeliveryPerTurn(I),
  () => consumedOnce(I),
  () => noNonMemberConsumed(I),
  () => membersNotSkipped(I)));

// ------------------------------------------------------------------ S6

const pendingAt = (I, pos) => {
  const before = (i) => i.pos < pos;
  const run = I.issues.filter(before).find((i) => i.cmd?.c === 'run'
    && !I.consumes.some((c) => c.pos < pos && c.entry?.e === 'notif'
      && c.entry.of === i.cmdIdx));
  const id = I.issues.filter(before).find((i) =>
    ['call', 'send'].includes(i.cmd?.c) && !(idConsumePos(I, i.cmdIdx) < pos));
  const causes = causeEntries(I).filter(before).length;
  const turns = I.segments.filter((s) => s.cause === 'journal' && s.start < pos);
  const queued = causes > turns.length;
  return run ?? id ?? (queued ? { causeQueue: causes - turns.length } : null);
};

const noSpuriousBlocked = (I) => firstFailure(
  I.violations.filter((v) => v.kind === 'blocked'), (v) => {
    const pending = pendingAt(I, v.pos);
    return pending
      ? fail('blocked-handler violation while something is pending',
        { violation: v.pos, pending })
      : null;
  });

// While frozen the executor waits for executing closures: they settle and
// their outcomes are proposed (a `done` is the closure's own completion), and
// the SDK may ask for a closure the wrapper
// then holds. Nothing else happens but deadline aborts.
const FREEZE_OK = new Set(['consume', 'abort', 'warn', 'done', 'settle', 'propose', 'wrapper']);

const quietWhileFrozen = (I) => firstFailure(
  I.ev.filter((e) => e.pos > I.freeze && e.pos <= I.cut), (e) => {
    if (!FREEZE_OK.has(e.t)) return fail('executor acted while frozen', e);
    return e.t === 'abort' && e.cause !== 'deadline'
      ? fail('non-deadline abort while frozen', e) : null;
  });

const S6 = perAttempt((I) => checks(
  () => noSpuriousBlocked(I),
  () => quietWhileFrozen(I)));

// ------------------------------------------------------------------ S7

const firstTurnFirst = (I) => {
  const firsts = I.segments.filter((s) => s.cause === 'first');
  if (I.segments.length && I.segments[0].cause !== 'first') {
    return fail('the first turn has another cause', I.segments[0]);
  }
  return firsts.length > 1 ? fail('two first turns', firsts) : null;
};

const localOnlyInClosing = (I) => firstFailure(I.segments, (s) =>
  (s.cause === 'local' && s.start < I.closing && s.start <= I.cut
    ? fail('local turn while the attempt is open', s) : null));

const turnTakesItsCause = (I, { seg, cause }) => {
  if (seg.start >= I.closing) return fail('journal turn during closing', seg);
  if (seg.entryIdx === undefined) return fail('journal turn names no cause', seg);
  if (!cause) {
    return fail('turn names an entry not consumed before it', { turn: seg.start });
  }
  if (!['cancel', 'result'].includes(cause.cls.kind)) {
    return fail('turn caused by an entry that is no cause', { seg, cause });
  }
  const ds = inSegment(seg, I.delivers);
  if (!turnCompleted(I, seg)) return ds.length > 1 ? fail('two deliveries', seg) : null;
  if (cause.cls.kind === 'cancel') {
    return ds.length ? fail('cancel turn delivered a result', { seg, ds }) : null;
  }
  const chained = ds.length === 0 && inSegment(seg, I.issues)
    .some((i) => i.cmd?.c === 'sleep' && i.cmd.op === cause.cls.op);
  const delivered = ds.length === 1 && ds[0].notif?.idx === cause.idx;
  return delivered || chained ? null
    : fail('turn did not act on the head of the cause queue',
      { turn: seg.start, cause: cause.idx, delivered: ds });
};

const deliveriesInJournalTurns = (I) => firstFailure(
  I.delivers.filter((d) => d.pos < I.closing), (d) =>
    (segmentAt(I, d.pos)?.cause === 'journal'
      ? null : fail('delivery outside a journal turn', d)));

const turnsInQueueOrder = (I) => firstFailure(journalSegments(I).slice(1), (seg) => {
  const prev = I.segments[seg.k - 1];
  const earlier = journalSegments(I).filter((s) => s.start < seg.start);
  const last = earlier.at(-1);
  return last && !(seg.entryIdx > last.entryIdx)
    ? fail('turns took causes out of queue order', { prev: last, seg, k: prev?.k })
    : null;
});

// A queued cause ahead of a turn's cause must have had its own turn, unless
// it was dropped: a result whose operation was released before this turn.
const noCauseSkipped = (I) => firstFailure(journalSegments(I), (seg) => {
  const taken = new Set(journalSegments(I).filter((s) => s.start < seg.start)
    .map((s) => s.entryIdx));
  const skipped = I.consumes.find((c) => c.pos < seg.start
    && c.idx < seg.entryIdx && !taken.has(c.idx) && (
      (c.cls.kind === 'cancel' && c.pos < Math.min(I.rootExit, I.freeze))
      || (c.cls.kind === 'result' && !(I.releases.get(c.cls.op) < seg.start))));
  return skipped ? fail('turn skipped a queued cause', { turn: seg.start, skipped }) : null;
});

const S7 = perAttempt((I) => checks(
  () => firstTurnFirst(I),
  () => turnsInQueueOrder(I),
  () => noCauseSkipped(I),
  () => localOnlyInClosing(I),
  () => firstFailure(matchTurns(I), (m) => turnTakesItsCause(I, m)),
  () => deliveriesInJournalTurns(I)));

// -------------------------------------------------------------- S8 clock

const MAX_LINK = 2 ** 31 - 1;
const hasOverflow = (I) => I.violations.some((v) => v.kind === 'overflow');
const clockClaim = (check) => perAttempt((I, h) =>
  (hasOverflow(I) ? null : check(I, h)));

const sampleIn = (I, seg) => (seg ? inSegment(seg, I.samples)[0] ?? null : null);

// L within a turn, read after its sample and its delivery, is the L every
// command that turn issues is anchored at (§4).
const exactAnchor = (I, seg) => {
  if (!seg) return undefined;
  const settled = Math.max(-1, ...inSegment(seg, [...I.samples, ...I.delivers])
    .map((e) => e.pos));
  return inSegment(seg, I.clocks).find((c) => c.pos > settled)?.L;
};

const isSleepLink = (cmd) => cmd?.c === 'sleep' && cmd.op !== 'deadline';

// Replays the attempt's observable clock facts in order: applied samples,
// sleep links issued (anchored at the exact L of their turn when a clock
// read shows it, else at the upper bound so far), links credited (on the
// delivery of their sleep or the issue of the next link), and clock reads.
const clockFacts = (I) => {
  const state = { maxSample: -Infinity, first: null, bound: -Infinity, last: null };
  const open = new Map();
  const credited = [];
  const reads = [];
  const credit = (op, pos) => (open.get(op) ?? []).splice(0).forEach((link) => {
    state.bound = Math.max(state.bound, link.anchor + link.ms);
    credited.push({ ...link, creditSeg: segmentAt(I, pos), creditPos: pos });
  });
  const onIssue = (e, cmd) => {
    credit(cmd.op, e.pos);
    const seg = segmentAt(I, e.pos);
    const anchor = exactAnchor(I, seg) ?? state.bound;
    const link = { op: cmd.op, ms: cmd.ms, anchor, issueSeg: seg, pos: e.pos };
    open.set(cmd.op, [...(open.get(cmd.op) ?? []), link]);
  };
  const onSample = (e) => {
    state.maxSample = Math.max(state.maxSample, e.reading);
    state.first ??= e.reading;
    state.bound = Math.max(state.bound, e.reading);
    state.last = e;
  };
  I.ev.forEach((e) => {
    if (e.t === 'sample') onSample(e);
    if (e.t === 'issue' && isSleepLink(I.cmdOf(e.cmdIdx))) onIssue(e, I.cmdOf(e.cmdIdx));
    if (e.t === 'deliver' && open.has(e.op)) credit(e.op, e.pos);
    if (e.t === 'clock' && state.last) {
      reads.push({ ...state, e, creditedCount: credited.length });
    }
  });
  return { reads, credited };
};

const P2 = clockClaim((I) => firstFailure(I.clocks.slice(1), (c) => {
  const prev = I.clocks[I.clocks.indexOf(c) - 1];
  return c.L < prev.L ? fail('L decreased', { from: prev, to: c }) : null;
}));

const linksOf = (I, op) => cmdEntries(I.att.journalOut)
  .filter((e) => isSleepLink(e.cmd) && e.cmd.op === op);

const linkCreditedInOrder = (I, links, j) => {
  const notif = I.att.journalOut.find((e) => e.e === 'notif' && e.of === links[j].idx);
  const next = issuePosOf(I, links[j + 1].idx);
  const seg = segmentAt(I, next);
  const sampled = seg && inSegment(seg, I.samples).some((s) => s.pos < next);
  return notif && consumePosOf(I, notif.idx) < next && sampled ? null
    : fail('next link issued before the previous link was credited',
      { link: links[j].idx });
};

const sleepLinksSum = (I, d) => {
  const stmt = I.prog.ops.get(d.op)?.stmt;
  if (stmt?.s !== 'sleep') return null;
  const links = linksOf(I, d.op);
  const total = links.reduce((sum, e) => sum + e.cmd.ms, 0);
  const rounded = Math.ceil(stmt.ms);
  if (total !== rounded) return fail('links do not sum to the duration', { d, total });
  const bad = rounded > 0 && links.find((e) => e.cmd.ms < 1 || e.cmd.ms > MAX_LINK);
  if (bad) return fail('link length out of range', bad);
  return firstFailure(links.slice(0, -1).map((_, j) => j),
    (j) => linkCreditedInOrder(I, links, j));
};

const P3 = clockClaim((I) => firstFailure(I.delivers,
  (d) => sleepLinksSum(I, d)));

const P4 = clockClaim((I) => firstFailure(clockFacts(I).reads, (r) =>
  (r.e.L < r.maxSample ? fail('L below an applied sample', r.e) : null)));

const leadOf = (I, link) => {
  const [a, b] = [sampleIn(I, link.issueSeg), sampleIn(I, link.creditSeg)];
  return a && b ? link.ms - (b.trueTime - a.trueTime) : null;
};

// P5 holds for every E and lead that satisfy its hypotheses, so it is checked
// with the smallest ones the history allows. A history whose true times
// decrease satisfies the claim vacuously.
const P5 = clockClaim((I) => {
  const times = I.samples.map((s) => s.trueTime);
  if (times.some((t, k) => k > 0 && t < times[k - 1])) return null;
  const E = Math.max(0, ...I.samples.map((s) => s.reading - s.trueTime));
  const { reads, credited } = clockFacts(I);
  const leads = credited.map((link) => leadOf(I, link));
  if (leads.includes(null)) return null;
  const lead = Math.max(0, ...leads);
  return firstFailure(reads, (r) => {
    const cap = r.last.trueTime + E + lead * r.creditedCount;
    return r.e.L > cap ? fail('L above true time + E + leads', { L: r.e.L, cap, E, lead }) : null;
  });
});

const withinP6 = (r) => {
  if (!Number.isInteger(r.e.L)) return fail('L is not an integer', r.e);
  if (r.first !== null && r.e.L < r.first) return fail('L below the first sample', r.e);
  return r.e.L > r.bound
    ? fail('L above max(samples, anchor + d of credited links)',
      { L: r.e.L, bound: r.bound, pos: r.e.pos })
    : null;
};

const P6 = clockClaim((I) => firstFailure(clockFacts(I).reads, withinP6));

const sampledBeforeDelivery = (I, d) => {
  const seg = segmentAt(I, d.pos);
  const s = seg && inSegment(seg, I.samples).find((x) => x.pos < d.pos);
  const issuedHere = s && inSegment(seg, I.issues)
    .some((i) => i.cmdIdx === s.cmdIdx && i.pos < s.pos);
  return issuedHere ? null
    : fail('delivery without a sample of its own turn', d);
};

const P7 = clockClaim((I) => firstFailure(
  I.delivers.filter((d) => d.pos < I.closing), (d) => sampledBeforeDelivery(I, d)));

const oneSamplePerTurn = (I) => firstFailure(
  I.segments.filter((s) => s.start <= I.cut), (seg) => {
    const ss = inSegment(seg, I.samples);
    if (seg.cause === 'local') return ss.length ? fail('local turn sampled', seg) : null;
    const done = seg.end <= I.cut;
    if (ss.length > 1 || (done && ss.length !== 1)) {
      return fail('turn without exactly one sample', { seg, samples: ss });
    }
    const own = ss.every((s) => inSegment(seg, I.issues).some((i) => i.cmdIdx === s.cmdIdx));
    return own ? null : fail('turn applied a sample another turn issued', seg);
  });

const releasedAddsNothing = (I) => firstFailure([...I.releases], ([op, r]) => {
  const late = I.delivers.find((d) => d.op === op && d.pos > r)
    ?? I.issues.find((i) => i.pos > r && isSleepLink(i.cmd) && i.cmd.op === op);
  return late ? fail('released operation delivered or continued', { op, late }) : null;
});

const releasedSleepNoCredit = (I) => {
  const sleeps = [...I.releases].filter(([op]) => I.prog.ops.get(op).stmt.s === 'sleep');
  const from = minPos(sleeps.map(([, r]) => r));
  return firstFailure(clockFacts(I).reads.filter((r) => r.e.pos > from), withinP6);
};

const P8 = clockClaim((I) => checks(
  () => oneSamplePerTurn(I),
  () => releasedAddsNothing(I),
  () => releasedSleepNoCredit(I)));

// ----------------------------------------------------------------- S11

const onlyCancelsWhileClosing = (I) => firstFailure(
  I.issues.filter((i) => i.pos >= I.closing || i.pos > I.cut), (i) =>
    (i.cmd && !(i.cmd.c === 'cancelCall' && i.cmd.by === 'executor')
      ? fail('command issued after closing latched', i) : null));

const consumedOnlyIssued = (I) => firstFailure(
  I.consumes.filter((c) => c.entry?.e === 'notif'), (c) =>
    (issuePosOf(I, c.entry.of) < c.pos ? null
      : fail('race awaited a command this attempt had not issued', c)));

const retiredChangesNothing = (I) => firstFailure([...I.releases], ([op, r]) => {
  const d = I.delivers.find((x) => x.op === op && x.pos > r);
  return d ? fail('result of a retired handle reached a fiber', { op, d }) : null;
});

const noDeliveryAfterLatch = (I) => {
  const refused = I.violations.some((v) => v.kind === 'refusedAtClosing');
  const late = I.delivers.find((d) => d.pos >= I.closing);
  return late && !refused ? fail('delivery after closing latched', late) : null;
};

const S11 = perAttempt((I) => checks(
  () => onlyCancelsWhileClosing(I),
  () => consumedOnlyIssued(I),
  () => retiredChangesNothing(I),
  () => noDeliveryAfterLatch(I)));

// ----------------------------------------------------------------- S12

const consumedInJournalOrder = (I) => firstFailure(
  I.consumes.filter((c, k) => k > 0 && c.pos <= I.cut), (c) => {
    const prev = I.consumes[I.consumes.indexOf(c) - 1];
    return c.idx <= prev.idx ? fail('entries consumed out of journal order', { prev, c }) : null;
  });

const deliveredInJournalOrder = (I) => {
  const open = I.delivers.filter((d) => d.pos < I.closing);
  const unmatched = open.find((d) => !d.notif);
  if (unmatched) return fail('delivery of a result the race never consumed', unmatched);
  const wrong = open.find((d) => !same(d.value, d.notif.entry.value));
  if (wrong) return fail('delivered value differs from the journal', wrong);
  return firstFailure(open.slice(1), (d) => {
    const prev = open[open.indexOf(d) - 1];
    return d.notif.idx < prev.notif.idx
      ? fail('results delivered out of journal order', { prev, d }) : null;
  });
};

const interruptInJournalOrder = (I) => {
  const cancel = causeEntries(I).find((c) => c.cls.kind === 'cancel');
  const at = rootCancelPos(I);
  if (!cancel || at === Infinity) return null;
  const wrong = I.delivers.filter((d) => d.pos < I.closing && d.notif).find((d) =>
    (d.notif.idx < cancel.idx) !== (d.pos < at));
  return wrong
    ? fail('root interrupted out of journal order', { cancel: cancel.idx, wrong })
    : null;
};

const neverDelivered = (I) => firstFailure(I.delivers, (d) => {
  if (isIdValue(d.value)) return fail('invocation id delivered to a fiber', d);
  if (d.op === 'deadline') return fail('deadline completion delivered', d);
  const r = I.releases.get(d.op);
  return r !== undefined && r < d.pos
    ? fail('result delivered after its fiber stopped awaiting it', d) : null;
});

const droppedWithoutTurn = (I) => firstFailure(matchTurns(I), ({ seg, cause }) => {
  const r = cause?.cls.kind === 'result' ? I.releases.get(cause.cls.op) : undefined;
  return r !== undefined && r < seg.start
    ? fail('turn for a result whose fiber stopped awaiting it', { turn: seg.start, cause })
    : null;
});

const S12 = perAttempt((I) => checks(
  () => consumedInJournalOrder(I),
  () => droppedWithoutTurn(I),
  () => deliveredInJournalOrder(I),
  () => interruptInJournalOrder(I),
  () => neverDelivered(I)));

// ----------------------------------------------------------------- S13

const cancelTurns = (I) => matchTurns(I).filter((m) => m.cause?.cls.kind === 'cancel');

const QUIET_IN_LATER_CANCEL = new Set(['deliver', 'interrupt', 'clock', 'draw']);

const laterCancelInert = (I, m) => {
  const loud = I.ev.slice(m.seg.start, m.seg.end).find((e) =>
    QUIET_IN_LATER_CANCEL.has(e.t)
    || (e.t === 'issue' && I.cmdOf(e.cmdIdx)?.op !== 'sample'));
  return loud ? fail('a later cancel signal changed what handler code observes',
    { turn: m.seg.start, event: loud }) : null;
};

const cancelInterruptsOnce = (I) => {
  const all = I.interrupts.filter((x) => x.cause === 'cancel');
  const roots = all.filter((x) => x.fiber === I.prog.root);
  if (roots.length > 1) return fail('root interrupted by cancellation twice', roots);
  const [firstTurn, ...later] = cancelTurns(I);
  const outside = all.find((x) => !firstTurn
    || x.pos < firstTurn.seg.start || x.pos >= firstTurn.seg.end);
  if (outside) return fail('cancellation interrupt outside the first cancel turn', outside);
  const daemon = all.find((x) => I.prog.daemon.get(x.fiber));
  if (daemon) return fail('cancellation interrupted a daemon fiber', daemon);
  if (firstTurn && roots.length === 0 && turnCompleted(I, firstTurn.seg)) return fail('first cancel turn did not interrupt the root', firstTurn.seg);
  return firstFailure(later, (m) => laterCancelInert(I, m));
};

const callsAfterCancelAreSends = (I) => {
  const consumed = minPos(I.consumes.filter((c) => c.cls.kind === 'cancel').map((c) => c.pos));
  return firstFailure(I.issues.filter((i) => i.pos > consumed), (i) => {
    const isCall = I.prog.ops.get(i.cmd?.op)?.stmt.s === 'call';
    return isCall && i.cmd.c === 'call'
      ? fail('call issued after a cancel signal was consumed is not a send', i) : null;
  });
};

// The SDK writes its cancel commands when it observes a cancel signal, so
// each SDK cancel new in this attempt belongs to the most recent cancel
// signal the race consumed before the command was written. It was written
// before the first trace event that names a later journal index. A command
// persisted from an earlier attempt was judged in the attempt that wrote it.
// Later signals cancel nothing new: an SDK cancel that belongs to the k-th
// signal (k >= 2) must not target a call issued before signal k - 1.
const writtenBefore = (I, idx) => minPos(I.ev.filter((e) =>
  (e.t === 'issue' && e.cmdIdx > idx) || (e.t === 'consume' && e.entryIdx > idx)).map((e) => e.pos));

const sdkCancelsOnlyFirst = (I) => {
  const inSet = new Set(I.att.journalIn.map((e) => e.idx));
  const signals = I.consumes.filter((c) => c.cls.kind === 'cancel').map((c) => c.pos);
  return firstFailure(cmdEntries(I.att.journalOut), (e) => {
    if (e.cmd.c !== 'cancelCall' || e.cmd.by !== 'sdk') return null;
    if (I.cmdOf(e.cmd.target)?.c !== 'call') return fail('SDK cancelled something that is not a call', e);
    if (inSet.has(e.idx)) return null;
    const point = writtenBefore(I, e.idx);
    const k = signals.filter((pos) => pos < point).length;
    const issued = I.issues.find((i) => i.cmdIdx === e.cmd.target)?.pos ?? -Infinity;
    return k >= 2 && issued < signals[k - 2]
      ? fail('a later cancel signal made the SDK cancel a call', { e, signal: k }) : null;
  });
};

const absorbedAfterExit = (I) => firstFailure(I.ev.filter((e) => e.pos > I.rootExit), (e) => {
  if (e.t === 'turn' && e.cause === 'journal') return fail('turn after the root exited', e);
  if (e.t === 'sample') return fail('sample after the root exited', e);
  return e.t === 'interrupt' && e.cause === 'cancel'
    ? fail('cancellation interrupt after the root exited', e) : null;
});

const S13 = perAttempt((I) => checks(
  () => cancelInterruptsOnce(I),
  () => callsAfterCancelAreSends(I),
  () => sdkCancelsOnlyFirst(I),
  () => absorbedAfterExit(I)));

// ----------------------------------------------------------------- S14

const PERSISTED_ENDS = new Set(['output', 'suspended']);

const S14a = perAttempt((I) => {
  const from = rootCancelPos(I);
  if (from === Infinity) return null;
  const refused = I.violations.find((v) => v.kind === 'refusedAtClosing'
    && v.pos > from && v.pos < I.rootExit
    && !I.violations.some((w) => w.pos < v.pos));
  if (refused) return fail('finalizer start refused while the attempt was open', refused);
  if (!PERSISTED_ENDS.has(I.att.end.kind)) return null;
  const lost = I.issues.find((i) => i.pos > from && i.pos < I.rootExit && !i.cmd);
  return lost ? fail('finalizer command not journaled', lost) : null;
});

const opCount = (journal, before) => cmdEntries(journal)
  .filter((e) => e.idx < before && DURABLE.has(e.cmd.c)).length;

const keyParts = (key) => {
  const cut = typeof key === 'string' ? key.lastIndexOf(':') : -1;
  return cut < 1 ? null : { id: key.slice(0, cut), n: key.slice(cut + 1) };
};

const sendKeyWellFormed = (journal, e) => {
  const parts = keyParts(e.cmd.key);
  const n = String(opCount(journal, e.idx));
  return parts && parts.n === n ? null
    : fail('send key is not <invocation id>:<n>', { send: e, expectedN: n });
};

const sendEntries = (journal) => cmdEntries(journal).filter((e) => e.cmd.c === 'send');

// Merges a journal's sends into a { key: idx } map, failing on a key that
// names two different sends.
const keysUnique = (sends) => {
  const byKey = {};
  return firstFailure(sends, ({ idx, key }) => {
    const other = byKey[key];
    byKey[key] = idx;
    return other !== undefined && other !== idx
      ? fail('two sends share a key', { key, idx: [other, idx] }) : null;
  });
};

const oneInvocationId = (sends) => {
  const ids = new Set(sends.map(({ key }) => keyParts(key)?.id));
  return ids.size > 1 ? fail('send keys name different invocation ids', [...ids]) : null;
};

const childKeysMatch = (children, sends) => firstFailure(
  (children ?? []).filter((c) => c.kind === 'send'), (child) => {
    const send = sends.find(({ idx }) => idx === child.viaCmd);
    return send && send.key !== child.key
      ? fail('child key differs from its send', { child, send }) : null;
  });

// Kept per attempt: its journal's sends as { idx, key }.
const S14b = {
  attempt: (I) => checks(
    () => callsAfterCancelAreSends(I),
    () => firstFailure(sendEntries(I.att.journalOut),
      (e) => sendKeyWellFormed(I.att.journalOut, e))),
  summarize: (I) => ({ sends: sendEntries(I.att.journalOut)
    .map((e) => ({ idx: e.idx, key: e.cmd.key })) }),
  across: (sums, cur) => {
    const all = [...sums, cur].flatMap((s) => s.sends);
    return checks(() => keysUnique(all), () => oneInvocationId(all));
  },
  final: (sums, h) => childKeysMatch(h.children, sums.flatMap((s) => s.sends)),
};

const cancelTargets = (journal) => cmdEntries(journal)
  .filter((e) => e.cmd.c === 'cancelCall').map((e) => e.cmd.target);

const attachedOnce = (I, idx) => {
  const key = I.cmdOf(idx)?.key;
  const attaches = cmdEntries(I.att.journalOut)
    .filter((e) => e.cmd.c === 'attach' && e.cmd.target === key);
  return attaches.length > 1 ? fail('compensation attached twice', attaches) : null;
};

const compChildIntact = (idx, targets, children, killed) => {
  if (targets.includes(idx)) return fail('compensation child cancelled', { send: idx });
  const child = (children ?? []).find((c) => c.viaCmd === idx);
  if (child?.cancelled) return fail('compensation child marked cancelled', child);
  return child?.killed && !killed
    ? fail('compensation child killed without a kill', child) : null;
};

// Kept per attempt: its compensation sends, its journal's cancel targets and
// whether it was killed; the children are judged at the end.
const cutSummary = (I) => ({ targets: cancelTargets(I.att.journalOut),
  killed: I.att.end.kind === 'killed' });

const attachDelivered = (I, idx) => {
  const send = I.cmdOf(idx);
  const op = send.op;
  const attach = cmdEntries(I.att.journalOut)
    .find((e) => e.cmd.c === 'attach' && e.cmd.target === send.key);
  const notif = attach && I.att.journalOut
    .find((e) => e.e === 'notif' && e.of === attach.idx);
  const q = notif ? consumePosOf(I, notif.idx) : Infinity;
  const owner = I.prog.ops.get(op)?.fiber;
  const interrupted = I.interrupts.some((x) => x.fiber === owner
    && x.pos > issuePosOf(I, idx) && x.pos < q);
  if (q === Infinity || interrupted || !(I.rootExit > q)) return null;
  const d = I.delivers.find((x) => x.op === op && x.pos > q);
  return d && d.pos < I.rootExit && same(d.value, notif.value) ? null
    : fail('finalizer did not receive the child outcome', { op, notif, d });
};

const S14d = {
  attempt: (I) => firstFailure([...compensations(I)],
    (idx) => attachedOnce(I, idx) ?? attachDelivered(I, idx)),
  summarize: (I) => ({ comps: [...compensations(I)], ...cutSummary(I) }),
  final: (sums, h) => {
    const targets = sums.flatMap((s) => s.targets);
    const killed = sums.some((s) => s.killed);
    return firstFailure(sums.flatMap((s) => s.comps),
      (idx) => compChildIntact(idx, targets, h.children, killed));
  },
};

// ----------------------------------------------------------------- S15

const overInterrupted = (I, fiber, pos) =>
  I.interrupts.some((x) => x.fiber === fiber && x.pos < pos)
  || (!I.prog.daemon.get(fiber) && rootCancelPos(I) < pos)
  || I.closing <= pos;

const cancelObligation = (I, op, r, comps) => {
  const iss = opIssue(I, op, new Set(['call', 'send']));
  if (!iss || comps.has(iss.cmdIdx) || r > I.cut) return null;
  if (resultConsumePos(I, op) < r) return null;
  // At once if the id has arrived, else as soon as it arrives: after both
  // the release and the id's consumption, before the race consumes again.
  const idPos = idConsumePos(I, iss.cmdIdx);
  const deadline = nextConsumeAfter(I, Math.max(r, idPos));
  const timely = executorCancels(I).some((x) => x.cmd.target === iss.cmdIdx
    && x.pos >= r && x.pos > idPos && x.pos < deadline);
  const owed = deadline <= I.cut || I.att.end.kind === 'output';
  const from = Math.max(r, idPos);
  return timely || !owed ? null
    : fail('interrupted fiber\'s call not cancelled', { op, release: r, from });
};

const cancelsAreOwed = (I, comps) => firstFailure(executorCancels(I), (x) => {
  const target = I.cmdOf(x.cmd.target);
  const op = target?.op;
  const owner = I.prog.ops.get(op)?.fiber;
  if (!['call', 'send'].includes(target?.c)) return fail('executor cancelled a non-call', x);
  if (comps.has(x.cmd.target)) return fail('executor cancelled a compensation', x);
  if (resultConsumePos(I, op) < x.pos) return fail('executor cancelled a completed call', x);
  return overInterrupted(I, owner, x.pos) ? null
    : fail('executor cancelled a call of a fiber it did not interrupt', x);
});

const cancelledNotDelivered = (I) => firstFailure(executorCancels(I), (x) => {
  const op = I.cmdOf(x.cmd.target)?.op;
  const d = I.delivers.find((y) => y.op === op && y.pos > x.pos);
  return d ? fail('a cancelled call\'s result reached a fiber', { x, d }) : null;
});

const childConflictIsNotCancellation = (I) => firstFailure(
  I.delivers.filter((d) => d.value?.terminal === '409'), (d) => {
    const seg = segmentAt(I, d.pos);
    const x = seg && inSegment(seg, I.interrupts).find((y) => y.cause === 'cancel');
    return x ? fail('a child\'s 409 became a cancellation', { d, x }) : null;
  });

const S15 = perAttempt((I) => {
  const comps = compensations(I);
  const calls = [...I.releases].filter(([op]) => I.prog.ops.get(op).stmt.s === 'call');
  return checks(
    () => firstFailure(calls, ([op, r]) => cancelObligation(I, op, r, comps)),
    () => cancelsAreOwed(I, comps),
    () => cancelledNotDelivered(I),
    () => childConflictIsNotCancellation(I));
});

// ----------------------------------------------------------------- S16

const expectedValue = (eff) => {
  if (eff.entered === false) return (v) => v?.terminal === ABORTED;
  if (eff.settled === 'ok') return (v) => !!v && 'ok' in v;
  if (eff.settled === 'terminal') return (v) => !!v && 'terminal' in v && v.terminal !== ABORTED;
  if (eff.settled === 'aborted') return (v) => v?.terminal === ABORTED;
  return () => false;
};

const resultJournaledBefore = (journal, op, limit) => {
  const notif = runResultIn(journal, op);
  return notif && notif.idx < limit ? notif : null;
};

const S16a = perAttempt((I) => {
  if (I.att.end.kind !== 'output') return null;
  const out = outputEntry(I.att.journalOut)?.idx ?? Infinity;
  const settled = effectsOf(I.att).filter((e) => e.entered === false
    || (e.entered && ['ok', 'terminal', 'aborted'].includes(e.settled)));
  return firstFailure(settled, (eff) =>
    (resultJournaledBefore(I.att.journalOut, eff.op, out) ? null
      : fail('settled run not journaled before output', eff)));
});

// What the next attempt shows about each run: whether it was entered or
// refused, and which runs newly have a terminal abort journaled.
const rerunInfo = (att) => ({
  n: att.n, kind: att.end.kind,
  tried: effectsOf(att).filter((e) => e.entered === true || e.entered === false)
    .map((e) => e.op),
  abortedNew: cmdEntries(att.journalOut).filter((e) => e.cmd.c === 'run')
    .map((e) => e.cmd.op)
    .filter((op) => newResult(att, op)?.value?.terminal === ABORTED),
});

// S16(d): "unless S20 applies". A run executes again, or the entry gate
// refuses it and its terminal abort is journaled.
const runsAgain = (prev, cur) => {
  if (!prev || cur.n !== prev.n + 1 || cur.kind !== 'output') return null;
  const missing = prev.owed.find((op) => !cur.tried.includes(op)
    && !cur.abortedNew.includes(op));
  return missing
    ? fail('run whose result was not journaled did not execute again',
      { op: missing, attempt: cur.n }) : null;
};

const journaledNotRerun = (att) => {
  const rerun = effectsOf(att).find((e) => e.entered === true
    && runResultIn(att.journalIn, e.op));
  return rerun ? fail('run with a journaled result executed again', { rerun }) : null;
};

// Kept per attempt: its number, end kind, and the runs it owes the next.
const rerunSpec = (owedBy) => ({
  summarize: (I) => ({ ...rerunInfo(I.att), owed: owedBy(I.att) }),
  across: (sums, cur) => runsAgain(sums.at(-1), cur),
  keep: (cur) => ({ n: cur.n, owed: cur.owed }),
});

const retriedAttempt = (I) => {
  const failed = effectsOf(I.att).filter((e) => e.settled === 'retryable');
  if (I.freeze !== Infinity && failed.length === 0) {
    return fail('freeze with no retryable closure failure');
  }
  return failed.length && PERSISTED_ENDS.has(I.att.end.kind)
    ? fail('attempt with a retryable closure failure was not retried', failed[0]) : null;
};

// --- closure lifecycle (wrapper, enter, refuse, settle, propose)

const lifecycle = (I, t) => I.ev.filter((e) => e.t === t);
const isSampleOp = (op) => typeof op === 'string' && op.startsWith('sample:');
const firstRetrySettle = (I) => lifecycle(I, 'settle')
  .find((e) => e.outcome === 'retryable' && e.pos <= I.cut) ?? null;
const HARD_STOP = new Set(['crashed', 'killed']);
const FROZEN_FORBIDS = new Set(['turn', 'deliver', 'issue', 'enter']);

// C18: from a retryable settle on, no turn, delivery, command or entry, and
// the freeze comes before the attempt ends (unless a crash or kill cuts it).
const frozenAfterRetrySettle = (I) => {
  const s = firstRetrySettle(I);
  if (!s) return null;
  const acted = I.ev.find((e) => e.pos > s.pos && e.pos <= I.cut && FROZEN_FORBIDS.has(e.t));
  if (acted) return fail('executor acted after a retryable settle', { settle: s, acted });
  const frozen = I.freeze > s.pos && I.freeze <= I.cut;
  return frozen || HARD_STOP.has(I.att.end.kind) ? null
    : fail('retryable settle not followed by a freeze before the end', s);
};

// M8: a settlement is learned at once, not at the next turn, so the freeze
// starts at the first retryable settle: no delivery follows it, and nothing
// but lifecycle events and consumption comes between the settle and the
// freeze. A freeze needs a retryable settle before it.
const FREEZE_PREFIX_OK = new Set(['done', 'settle', 'propose', 'wrapper', 'consume', 'warn']);
const freezeAtFirstRetrySettle = (I) => {
  const s = firstRetrySettle(I);
  const hasLifecycle = I.ev.some((e) => e.t === 'settle');
  if (!s) {
    return hasLifecycle && I.freeze <= I.cut
      ? fail('freeze without a retryable settle before it') : null;
  }
  if (I.freeze < s.pos) return fail('freeze before the first retryable settle', s);
  const late = I.delivers.find((d) => d.pos > s.pos && d.pos <= I.cut);
  if (late) return fail('delivery after a retryable settle', { settle: s, late });
  const between = I.ev.find((e) => e.pos > s.pos && e.pos < Math.min(I.freeze, I.cut + 1)
    && !FREEZE_PREFIX_OK.has(e.t));
  return between ? fail('freeze did not start at the retryable settle', { settle: s, between }) : null;
};

// M8, from the closure's side: the executor learns of a completion once the
// turn running when the closure completed has finished its synchronous work,
// so events of that same turn may follow a `done` (a closure aborted by the
// turn can finish inside it). No new turn, of any cause, starts between a
// closure's `done` and its `settle`; a delivery in a later turn would need
// one. And the first retryable settlement acted on is that of the first
// closure that completed retryably.
const DONE_GAP_FORBIDS = new Set(['turn']);
const settleOf = (I, d) => I.ev.find((e) => e.pos > d.pos && e.t === 'settle'
  && e.cmdIdx === d.cmdIdx) ?? null;

const settledAtOnce = (I) => firstFailure(
  lifecycle(I, 'done').filter((d) => d.pos <= I.cut), (d) => {
    const until = settleOf(I, d)?.pos ?? I.cut + 1;
    const held = I.ev.find((e) => e.pos > d.pos && e.pos < until && DONE_GAP_FORBIDS.has(e.t));
    return held ? fail('settlement held past an executor action', { done: d, held }) : null;
  });

const freezeAtFirstRetryDone = (I) => {
  const d = lifecycle(I, 'done').find((e) => e.outcome === 'retryable' && e.pos <= I.cut);
  const s = d && settleOf(I, d);
  const first = firstRetrySettle(I);
  return s && first && first.pos < s.pos
    ? fail('freeze did not start at the first retryable completion', { done: d, first }) : null;
};

// M2: in an attempt that ends "retry", every success and terminal failure
// that settled in the attempt, before the freeze or during it, is proposed
// before the first retryable proposal.
const proposedInOrder = (I) => {
  if (I.att.end.kind !== 'retry') return null;
  const proposes = lifecycle(I, 'propose');
  if (!proposes.length) return null;
  const firstRetry = proposes.find((e) => e.outcome === 'retryable')?.pos ?? Infinity;
  const settledEarly = lifecycle(I, 'settle').filter((e) => e.pos <= I.cut
    && ['ok', 'terminal'].includes(e.outcome) && !isSampleOp(e.op));
  return firstFailure(settledEarly, (st) => {
    const p = proposes.find((e) => e.cmdIdx === st.cmdIdx && e.outcome !== 'retryable');
    return p && p.pos < firstRetry ? null
      : fail('a settled outcome was not proposed before the retryable failure',
        { settle: st, propose: p ?? null });
  });
};

const S16b = {
  attempt: (I) => checks(
    () => quietWhileFrozen(I),
    () => settledAtOnce(I),
    () => freezeAtFirstRetryDone(I),
    () => freezeAtFirstRetrySettle(I),
    () => frozenAfterRetrySettle(I),
    () => proposedInOrder(I),
    () => retriedAttempt(I)),
  ...rerunSpec((att) => (att.end.kind === 'retry'
    ? effectsOf(att).filter((e) => e.settled === 'retryable').map((e) => e.op) : [])),
};

const S16c = perAttempt((I) => {
  if (I.att.end.kind !== 'suspended') return null;
  return firstFailure(effectsOf(I.att), (eff) => {
    if (eff.entered && eff.settled === null) return fail('closure executing at suspension', eff);
    if (eff.entered === null) return null;
    const notif = runResultIn(I.att.journalOut, eff.op);
    return notif && expectedValue(eff)(notif.value) ? null
      : fail('settled run lost at suspension', eff);
  });
});

const unjournaledRuns = (att) => effectsOf(att)
  .filter((e) => e.entered && !runResultIn(att.journalOut, e.op)).map((e) => e.op);

const rerunAfter = (kind) => ({
  trace: false,
  attempt: (I) => journaledNotRerun(I.att),
  ...rerunSpec((att) => (att.end.kind === kind ? unjournaledRuns(att) : [])),
});

const S16d = rerunAfter('ended');
const S16e = rerunAfter('crashed');

// Kept per attempt: whether it was killed.
const S16f = {
  trace: false,
  summarize: (I) => ({ killed: I.att.end.kind === 'killed' }),
  across: (sums) => (sums.some((s) => s.killed) ? fail('an attempt followed a kill') : null),
  keep: (cur) => ({ killed: cur.killed }),
};

// ----------------------------------------------------------------- S17

const retainedRun = (I, op, r) => {
  const later = I.delivers.find((d) => d.op === op && d.pos > r);
  if (later) return fail('retained run delivered to a fiber', later);
  const notif = runResultIn(I.att.journalOut, op);
  const passed = notif && I.consumes.some((c) => c.idx > notif.idx && c.pos <= I.cut);
  if (passed && !(consumePosOf(I, notif.idx) <= I.cut)) {
    return fail('retained run left the race unconsumed', { op, notif });
  }
  if (I.att.end.kind !== 'output') return null;
  const out = outputEntry(I.att.journalOut)?.idx ?? Infinity;
  return notif && notif.idx < out && consumePosOf(I, notif.idx) <= I.cut ? null
    : fail('output written before a retained run\'s result was consumed', { op });
};

const S17 = perAttempt((I) => firstFailure([...I.releases].filter(([op, r]) =>
  I.prog.ops.get(op).stmt.s === 'run' && !(resultConsumePos(I, op) < r)),
([op, r]) => retainedRun(I, op, r)));

// ----------------------------------------------------------------- S18

const deadlineConsumePos = (I, op) => minPos(I.consumes
  .filter((c) => c.cls.kind === 'deadline' && I.deadlineRun.get(c.entry.of) === op)
  .map((c) => c.pos));

const abortJustified = (I, a) => {
  const issued = opIssue(I, a.op, new Set(['run']))?.pos ?? Infinity;
  if (I.prog.ops.get(a.op)?.stmt.s !== 'run') return 'abort of something not a run';
  if (a.cause === 'ended') {
    return I.att.end.kind === 'ended' && a.pos > I.cut ? null : 'ended abort without an Ended cut';
  }
  if (a.cause === 'deadline') {
    const q = deadlineConsumePos(I, a.op);
    return q <= a.pos && !(resultConsumePos(I, a.op) < q) ? null : 'deadline abort without its cause';
  }
  const owner = I.prog.ops.get(a.op).fiber;
  const released = I.releases.get(a.op) <= a.pos;
  const hit = released
    || I.interrupts.some((x) => x.fiber === owner && x.pos > issued && x.pos <= a.pos);
  return hit && !(resultConsumePos(I, a.op) < a.pos) ? null : 'interrupt abort without an interrupt';
};

const abortsJustified = (I) => firstFailure(I.aborts, (a) => {
  const why = abortJustified(I, a);
  return why ? fail(why, a) : null;
});

const abortedWhenDue = (I) => {
  const aborted = (op) => I.aborts.some((a) => a.op === op);
  const runs = [...I.releases].filter(([op, r]) =>
    I.prog.ops.get(op).stmt.s === 'run'
    && !(resultConsumePos(I, op) < r) && r <= I.cut);
  const fromRelease = runs.find(([op]) => !aborted(op));
  if (fromRelease) return fail('interrupted fiber\'s run not aborted', fromRelease);
  const dueByDeadline = [...new Set(I.deadlineRun.values())].find((op) => {
    const q = deadlineConsumePos(I, op);
    return q <= I.cut && !(resultConsumePos(I, op) < q) && !aborted(op);
  });
  return dueByDeadline ? fail('run past its consumed deadline not aborted', dueByDeadline) : null;
};

const newResult = (att, op) => {
  const notif = runResultIn(att.journalOut, op);
  return notif && !runResultIn(att.journalIn, op) ? notif : null;
};

const classifiedByOwnRecord = (I) => firstFailure(effectsOf(I.att), (eff) => {
  const notif = newResult(I.att, eff.op);
  if (!notif || eff.entered === null || (eff.entered && eff.settled === null)) return null;
  const recorded = I.aborts.some((a) => a.op === eff.op);
  if (notif.value?.terminal === ABORTED && !recorded) {
    return fail('terminal abort with no abort the executor recorded', eff);
  }
  return expectedValue(eff)(notif.value) ? null
    : fail('failure classified against the record', { eff, value: notif.value });
});

const S18 = perAttempt((I) => checks(
  () => abortsJustified(I),
  () => abortedWhenDue(I),
  () => classifiedByOwnRecord(I)));

// ----------------------------------------------------------------- S19

const deadlineMatchesProgram = (I) => firstFailure([...I.deadlineRun], ([idx, op]) => {
  const want = I.prog.ops.get(op).stmt.deadline;
  return I.cmdOf(idx).ms === want ? null
    : fail('deadline sleep length differs from the run\'s deadline', { idx, op });
});

const S19 = perAttempt((I) => checks(
  () => deadlineMatchesProgram(I),
  () => firstFailure(I.aborts.filter((a) => a.cause === 'deadline'), (a) => {
    const q = deadlineConsumePos(I, a.op);
    if (!(q <= a.pos)) return fail('deadline abort before its completion was consumed', a);
    return resultConsumePos(I, a.op) < q
      ? fail('deadline abort after the run\'s result was consumed', a) : null;
  })));

// ----------------------------------------------------------------- S20

const entryRespectsSignal = (I) => firstFailure(effectsOf(I.att), (eff) => {
  if (eff.entered && eff.signalAbortedAtEntry) return fail('closure entered with its signal aborted', eff);
  if (eff.entered !== false) return null;
  if (!eff.signalAbortedAtEntry) return fail('closure refused with its signal live', eff);
  return I.aborts.some((a) => a.op === eff.op) ? null
    : fail('closure refused with no abort the executor recorded', eff);
});

const refusedJournaled = (I) => {
  if (!PERSISTED_ENDS.has(I.att.end.kind)) return null;
  return firstFailure(effectsOf(I.att).filter((e) => e.entered === false), (eff) =>
    (runResultIn(I.att.journalOut, eff.op)?.value?.terminal === ABORTED ? null
      : fail('refused run\'s terminal abort not journaled', eff)));
};

// An abort whose cause the journal holds: a deadline, or an interruption by
// a lost race or a cancellation, recorded while the attempt was still its
// own, with every entry consumed before it persisted in the later journal.
const journaledAborts = (I) => I.aborts.filter((a) => a.pos <= I.cut).filter((a) => {
  if (a.cause === 'deadline') return true;
  // A lost race, or the owning fiber's completion, which interrupts the
  // fibers it forked (an unawaited operation is such a child).
  if (['race', 'exit'].includes(I.releaseCause.get(a.op))
    && I.releases.get(a.op) <= a.pos) return true;
  const owner = I.prog.ops.get(a.op)?.fiber;
  const x = I.interrupts.filter((y) => y.fiber === owner && y.pos <= a.pos).at(-1);
  return a.cause === 'interrupt'
    && ['race', 'cancel', 'closing'].includes(x?.cause);
});

// Kept per attempt: each journaled abort's run and the journal indices
// consumed before it. A later attempt whose journalIn holds them all and no
// result for the run must not enter its closure.
const abortSummary = (I) => journaledAborts(I).map((a) => ({
  op: a.op, needs: I.consumes.filter((c) => c.pos < a.pos).map((c) => c.idx),
}));

const replaySummary = (att) => ({
  n: att.n,
  inIdx: att.journalIn.map((e) => e.idx),
  resultIn: cmdEntries(att.journalIn).filter((e) => e.cmd.c === 'run')
    .map((e) => e.cmd.op).filter((op) => runResultIn(att.journalIn, op)),
  entered: effectsOf(att).filter((e) => e.entered).map((e) => e.op),
});

const reAborted = (aborts, cur) => firstFailure(aborts, (a) => {
  const persisted = a.needs.every((idx) => cur.inIdx.includes(idx));
  if (!persisted || cur.resultIn.includes(a.op)) return null;
  return cur.entered.includes(a.op)
    ? fail('closure re-entered although the journal holds its abort',
      { abort: a, attempt: cur.n }) : null;
});

// C24: a closure is entered only once every cause consumed before its entry
// has been acted on: a turn's cause when that turn has applied its sample and
// done its delivery or interruption; a cancel signal no turn names only
// after the root's exit (absorbed). Samples pass the gate (M7).
const turnActedBy = (I, seg, pos) => {
  const sample = inSegment(seg, I.samples)[0];
  const action = I.ev.find((e) => e.pos > seg.start && e.pos < seg.end
    && ['deliver', 'interrupt'].includes(e.t));
  return !!sample && sample.pos < pos && (!action || action.pos < pos);
};

const gateRespected = (I) => firstFailure(
  lifecycle(I, 'enter').filter((e) => !isSampleOp(e.op)), (en) => {
    const segs = journalSegments(I);
    const named = new Set(segs.map((s) => s.entryIdx));
    const pending = segs.find((seg) => consumePosOf(I, seg.entryIdx) < en.pos
      && !turnActedBy(I, seg, en.pos));
    if (pending) return fail('closure entered before a consumed cause was acted on', { enter: en, turn: pending.start });
    const cancel = I.consumes.find((c) => c.cls.kind === 'cancel' && c.pos < en.pos
      && !named.has(c.idx) && en.pos < I.rootExit);
    return cancel ? fail('closure entered while a cancel signal waited', { enter: en, cancel }) : null;
  });

// M7: a sample's closure passes the gate at once and is never held: its
// enter follows its wrapper with no consumption or turn between, and no
// attempt ends, however it ends, with a sample's wrapper not yet entered.
const SAMPLE_WAITS = new Set(['consume', 'turn']);
const samplesPassGate = (I) => firstFailure(
  lifecycle(I, 'wrapper').filter((w) => isSampleOp(w.op) && w.pos <= I.cut), (w) => {
    const en = I.ev.find((e) => e.pos > w.pos && e.t === 'enter' && e.cmdIdx === w.cmdIdx);
    if (!en || en.pos > I.cut) return fail('attempt ended while a sample\'s wrapper was held', w);
    const waited = I.ev.find((e) => e.pos > w.pos && e.pos < en.pos && SAMPLE_WAITS.has(e.t));
    return waited ? fail('sample waited at the gate', { wrapper: w, waited }) : null;
  });

const S20 = {
  attempt: (I) => checks(
  () => gateRespected(I),
  () => samplesPassGate(I),
  () => entryRespectsSignal(I),
  () => refusedJournaled(I)),
  summarize: (I) => ({ aborts: abortSummary(I), ...replaySummary(I.att) }),
  across: (sums, cur) => reAborted(sums.flatMap((s) => s.aborts), cur),
  keep: (cur) => ({ aborts: cur.aborts }),
};

// ----------------------------------------------------------------- S21

const expectedOutcome = (I) => {
  const violated = I.violations.some((v) => v.pos <= I.cut);
  const exit = I.ev.find((e) => e.t === 'rootExit');
  if (violated) return 'defect';
  if (!exit) return null;
  if (exit.outcome.kind === 'defect') return 'defect';
  return rootCancelPos(I) < I.rootExit ? 'cancelled' : exit.outcome.kind;
};

const outcomeOfAttempt = (I) => {
  const kind = I.att.end.kind;
  if (kind === 'retry') {
    return outputEntry(I.att.journalOut) ? fail('a retried attempt wrote output') : null;
  }
  if (kind !== 'output') return null;
  const want = expectedOutcome(I);
  const out = outputEntry(I.att.journalOut);
  if (!want) return fail('output with no root exit and no violation');
  return out && out.outcome.kind !== want
    ? fail('output outcome breaks precedence', { want, out }) : null;
};

const finalOutcome = (last, outcome) => {
  if (last?.kind === 'retry') {
    return outcome ? fail('retried attempt decided a final outcome', outcome) : null;
  }
  return last?.kind === 'output' && outcome?.kind !== last.want
    ? fail('final outcome breaks precedence', { want: last.want, got: outcome }) : null;
};

// Kept: the last attempt's end kind and the outcome it requires.
const S21 = {
  attempt: outcomeOfAttempt,
  summarize: (I) => ({ kind: I.att.end.kind,
    want: I.att.end.kind === 'output' ? expectedOutcome(I) : null }),
  keep: (cur) => cur,
  final: (sums, h) => finalOutcome(sums.at(-1), h.outcome),
};

// ----------------------------------------------------------------- S22

const nothingAfterHardStop = (I) =>
  (['crashed', 'killed'].includes(I.att.end.kind) && I.ev.length - 1 > I.cut
    ? fail('events after a crash or kill', { at: I.cut, events: I.ev.slice(I.cut + 1) })
    : null);

const endedAbortsExecuting = (I) => {
  if (I.att.end.kind !== 'ended') return null;
  const stuck = effectsOf(I.att).find((e) => e.entered && e.settled === null
    && !I.aborts.some((a) => a.op === e.op));
  return stuck ? fail('run executing at an Ended cut was not aborted', stuck) : null;
};

const afterCutNotJournaled = (I) => firstFailure(
  I.issues.filter((i) => i.pos > I.cut), (i) =>
    (I.jmap.has(i.cmdIdx) ? fail('command issued after the cut reached the journal', i) : null));

const childrenOnlyCancelledByCommand = (children, targets, killed) =>
  firstFailure(children ?? [], (c) => {
    if (c.cancelled && !targets.includes(c.viaCmd)) return fail('child cancelled by a cut', c);
    return c.killed && !killed ? fail('child killed without a kill', c) : null;
  });

// Kept per attempt: its journal's cancel targets and whether it was killed.
const S22 = {
  attempt: (I) => checks(
    () => nothingAfterHardStop(I),
    () => endedAbortsExecuting(I),
    () => afterCutNotJournaled(I),
    () => firstFailure(I.aborts.filter((a) => a.cause === 'ended'), (a) =>
      (I.att.end.kind === 'ended' && a.pos > I.cut ? null
        : fail('ended abort outside an Ended cut', a)))),
  summarize: cutSummary,
  final: (sums, h) => childrenOnlyCancelledByCommand(h.children,
    sums.flatMap((s) => s.targets), sums.some((s) => s.killed)),
};

// ----------------------------------------------------------------- S23

const liveAtExit = (I) => {
  const pending = I.issues.filter((i) => i.pos < I.rootExit && I.prog.ops.has(i.cmd?.op))
    .map((i) => i.cmd.op)
    .filter((op) => !(I.deliveredAt.get(op) < I.rootExit)
      && !(I.releases.get(op) < I.rootExit) && !(resultConsumePos(I, op) < I.rootExit));
  return new Set(pending.map((op) => I.prog.ops.get(op).fiber)
    .filter((f) => f !== I.prog.root));
};

const outputWaited = (I) => {
  const out = outputEntry(I.att.journalOut)?.idx ?? Infinity;
  return firstFailure(effectsOf(I.att), (eff) => {
    if (eff.entered && eff.settled === null) return fail('output before a closure settled', eff);
    if (eff.settled === 'retryable' || eff.entered === null) return null;
    const notif = resultJournaledBefore(I.att.journalOut, eff.op, out);
    return notif && consumePosOf(I, notif.idx) <= I.cut ? null
      : fail('output before a settled run was acknowledged', eff);
  });
};

const closingCancelsCalls = (I) => {
  const out = outputEntry(I.att.journalOut)?.idx ?? Infinity;
  const comps = compensations(I);
  const owed = [...I.releases].filter(([op, r]) => r > I.rootExit
    && I.prog.ops.get(op).stmt.s === 'call' && !(resultConsumePos(I, op) < r));
  return firstFailure(owed, ([op]) => {
    const iss = opIssue(I, op, new Set(['call', 'send']));
    if (!iss || comps.has(iss.cmdIdx)) return null;
    const c = cmdEntries(I.att.journalOut).find((e) => e.cmd.c === 'cancelCall'
      && e.cmd.by === 'executor' && e.cmd.target === iss.cmdIdx && e.idx < out);
    return c && idConsumePos(I, iss.cmdIdx) <= I.cut ? null
      : fail('output before a closing cancel was issued', { op });
  });
};

// M14: Output waits until every retained run's result has been consumed.
const retainedConsumed = (I) => {
  const out = outputEntry(I.att.journalOut)?.idx ?? Infinity;
  const retained = [...I.releases].filter(([op, r]) =>
    I.prog.ops.get(op).stmt.s === 'run' && !(resultConsumePos(I, op) < r));
  return firstFailure(retained, ([op]) => {
    const notif = resultJournaledBefore(I.att.journalOut, op, out);
    return notif && consumePosOf(I, notif.idx) <= I.cut ? null
      : fail('output before a retained run\'s result was consumed', { op });
  });
};

const exitOutput = (I) => {
  if (I.att.end.kind !== 'output' || I.rootExit === Infinity) return null;
  const notInterrupted = [...liveAtExit(I)].find((f) => !I.interrupts
    .some((x) => x.fiber === f && x.pos > I.rootExit && x.cause === 'closing'));
  if (notInterrupted) return fail('live fiber not interrupted at exit', { fiber: notInterrupted });
  return checks(() => outputWaited(I), () => retainedConsumed(I),
    () => closingCancelsCalls(I));
};

const refusedIsDefect = (I) => {
  const refused = I.violations.find((v) => v.kind === 'refusedAtClosing');
  if (!refused) return null;
  if (refused.pos < I.rootExit && !I.violations.some((v) => v.pos < refused.pos)) {
    return fail('start refused before closing', refused);
  }
  const out = outputEntry(I.att.journalOut);
  return out && out.outcome.kind !== 'defect'
    ? fail('refused start did not make the outcome a defect', out) : null;
};

const cancelledExitIsCancellation = (I) => {
  const out = outputEntry(I.att.journalOut);
  if (!out || !(rootCancelPos(I) < I.rootExit)) return null;
  const want = I.violations.some((v) => v.pos <= I.cut) ? 'defect' : 'cancelled';
  return out.outcome.kind === want ? null
    : fail('exit after a cancellation reported the wrong outcome', { want, out });
};

const S23 = perAttempt((I) => checks(
  () => onlyCancelsWhileClosing(I),
  () => exitOutput(I),
  () => refusedIsDefect(I),
  () => cancelledExitIsCancellation(I)));

// ------------------------------------------------------------ S25, S26

const namesOnlyAbortedUnsettled = (I, w) => firstFailure(w.runs, (op) => {
  if (!I.aborts.some((a) => a.op === op && a.pos < w.pos)) return fail('warning names a run not aborted', { w, op });
  if (!effectsOf(I.att).some((e) => e.op === op && e.entered)) return fail('warning names a run that never executed', { w, op });
  return resultConsumePos(I, op) < w.pos ? fail('warning names a settled run', { w, op }) : null;
});

const S25 = perAttempt((I) => {
  const ws = I.warns.filter((w) => w.which === 1);
  if (ws.length > 1) return fail('first warning emitted twice', ws);
  if (!ws.length) return null;
  const [w] = ws;
  if (!w.runs.length) return fail('first warning names no run', w);
  const holding = effectsOf(I.att).filter((e) => e.entered && e.settled === null
    && I.aborts.some((a) => a.op === e.op && a.pos < w.pos)).map((e) => e.op);
  const left = holding.find((op) => !w.runs.includes(op));
  if (left) return fail('first warning omits an aborted run holding the attempt', { w, op: left });
  return namesOnlyAbortedUnsettled(I, w);
});

const S26 = perAttempt((I) => {
  const ws = I.warns.filter((w) => w.which === 2);
  const named = ws.flatMap((w) => w.runs);
  const twice = named.find((op, k) => named.indexOf(op) !== k);
  if (twice) return fail('second warning emitted twice for a run', { op: twice });
  return firstFailure(ws, (w) => namesOnlyAbortedUnsettled(I, w));
});

// ------------------------------------------------------------- exports

const P = (id, statement, spec) => ({ id, statement, spec, check: runSpec(spec) });
const Pair = (id, statement, check) => ({ id, statement, check });

/** One predicate per checked statement of #48 part 2. */
export const predicates = [
  P('S1', 'Same inputs, same trace up to the common cut (across attempts)', S1),
  P('S2', 'Replay issues the journal\'s commands in order', S2),
  P('S3', 'A violation is at the same position in attempts with the same inputs', S3),
  P('S4', 'One race; its members only; at most one delivery per turn', S4),
  P('S6', 'Next transition: no spurious blocked violation; quiet while frozen', S6),
  P('S7', 'One cause per turn, taken from the head of the cause queue', S7),
  P('S8.P2', 'L never decreases', P2),
  P('S8.P3P9', 'Credited links sum to the rounded duration, each in range', P3),
  P('S8.P4', 'L is at least every applied sample', P4),
  P('S8.P5', 'L <= true time + E + lead per credited link', P5),
  P('S8.P6', 'L integer, >= first sample, <= max(samples, a + d)', P6),
  P('S8.P7', 'Every delivery follows its own turn\'s sample', P7),
  P('S8.P8', 'One sample per journal turn; released sleeps add nothing', P8),
  P('S10', 'Each fiber gets the same draws under the same inputs', S10),
  P('S11', 'Only race members awaited; closing issues only cancels', S11),
  P('S12', 'Journal order for consumption, delivery and interruption', S12),
  P('S13', 'One cancellation, as one interruption of the root', S13),
  P('S14a', 'Finalizers can issue durable operations after cancellation', S14a),
  P('S14b', 'Calls after a cancel are sends keyed <invocation id>:<n>', S14b),
  P('S14d', 'Compensation outcome reaches its finalizer; child never cancelled', S14d),
  P('S15', 'Interrupted fiber\'s calls cancelled, and no others', S15),
  P('S16a', 'Settled runs journaled before output', S16a),
  P('S16b', 'Freeze: quiet, then retried; failed runs execute again', S16b),
  P('S16c', 'Suspension: nothing executing, nothing lost', S16c),
  P('S16d', 'Ended cut: unjournaled runs execute again', S16d),
  P('S16e', 'Crash: unjournaled runs execute again', S16e),
  P('S16f', 'Kill: the run never executes again', S16f),
  P('S17', 'Retained runs stay in the race and reach no fiber', S17),
  P('S18', 'Aborts only for their three causes; classification by record', S18),
  P('S19', 'Deadline aborts only after the completion is consumed first', S19),
  P('S20', 'Entry gate and re-abort on replay', S20),
  P('S21', 'Final outcome by precedence', S21),
  P('S22', 'What each cut does', S22),
  P('S23', 'Exit, closing and finalizers', S23),
  P('S25', 'First warning', S25),
  P('S26', 'Second warning', S26),
];

const samePrograms = (pred) => (a, b) =>
  (same(a.program, b.program) ? pred(a, b) : null);

const acrossHistories = (compare) => samePrograms((A, B) =>
  firstFailure(A.attempts.flatMap((a) => B.attempts.map((b) => [a, b])), ([a, b]) => {
    const r = compare(ix(A, a), ix(B, b));
    return r && fail(r.msg, { attempts: [a.n, b.n], ...r.detail });
  }));

/**
 * Predicates over two histories of the same program. Every attempt of one is
 * compared with every attempt of the other under "same inputs up to a point"
 * (see compareProjections). That relation includes the seed, so the two histories
 * must share the invocation id; send keys compared by S2 assume it.
 */
const projected2 = (compare) => (a, b) =>
  compare(attemptProjection(a), attemptProjection(b));

export const pairPredicates = [
  Pair('S1', 'Same inputs, same trace up to the common cut',
    acrossHistories(projected2((a, b) => compareProjections(a, b, false)))),
  Pair('S2', 'Same inputs, same commands at the same positions',
    acrossHistories(projected2((a, b) => compareProjections(a, b, true)))),
  Pair('S3', 'Violations at the same positions', acrossHistories(projected2(compareViolations))),
  Pair('S10', 'Same draws per fiber', acrossHistories(projected2(compareDraws))),
];

// ---------------------------------------------------------- boundaries

const cancelTags = (I) => {
  const tags = [];
  const cancels = I.consumes.filter((c) => c.cls.kind === 'cancel');
  const pendingSample = (pos) => I.issues.some((i) => i.cmd?.op === 'sample'
    && i.cmd.c === 'run' && i.pos < pos
    && !I.samples.some((s) => s.cmdIdx === i.cmdIdx && s.pos < pos));
  if (cancels.some((c) => c.pos > rootCancelPos(I) && c.pos < I.rootExit)) tags.push('cancel:unwinding');
  if (cancels.some((c) => pendingSample(c.pos))) tags.push('cancel:duringSample');
  if (cancels.some((c) => c.pos > I.rootExit)) tags.push('cancel:afterRootExit');
  if (I.att.journalOut.filter((e) => e.e === 'cancel').length > 1) tags.push('cancel:twice');
  return tags;
};

const sleepTags = (I) => {
  const tags = [];
  const sleeps = I.issues.filter((i) => isSleepLink(i.cmd));
  const ends = (op) => Math.min(I.deliveredAt.get(op) ?? Infinity, I.releases.get(op) ?? Infinity);
  const overlap = sleeps.some((a) => sleeps.some((b) => a.cmd.op !== b.cmd.op
    && a.pos <= b.pos && b.pos < ends(a.cmd.op)));
  if (overlap) tags.push('sleep:overlap');
  const ops = sleeps.map((i) => i.cmd.op);
  if (ops.some((op, k) => ops.indexOf(op) !== k)) tags.push('sleep:chain');
  return tags;
};

const runTags = (I) => {
  const retained = [...I.releases].filter(([op, r]) => I.prog.ops.get(op).stmt.s === 'run'
    && !(resultConsumePos(I, op) < r)).map(([op]) => op);
  const tags = retained.length ? ['run:retained'] : [];
  if (effectsOf(I.att).some((e) => e.entered === false && retained.includes(e.op))) tags.push('run:unstartedRetained');
  return tags;
};

const programTags = (I) => {
  const tags = [];
  const protectedPending = I.interrupts.some((x) => [...I.prog.ops.values()].some((info) =>
    info.fiber === x.fiber && info.protected && !info.finalizer
    && issuePosOf(I, opIssue(I, info.op)?.cmdIdx) < x.pos
    && !(I.deliveredAt.get(info.op) < x.pos)));
  if (protectedPending) tags.push('uninterruptible');
  const issuedProtected = I.issues.some((i) => I.prog.ops.get(i.cmd?.op)?.protected
    && !I.prog.ops.get(i.cmd.op).finalizer);
  if (issuedProtected) tags.push('uninterruptible:issued');
  const raced = [...I.prog.ops.values()].some((info) => info.partner
    && I.deliveredAt.has(info.partner) && !I.deliveredAt.has(info.op)
    && opIssue(I, info.op));
  const lostRace = [...I.releaseCause.values()].includes('race');
  if (raced || lostRace || I.interrupts.some((x) => x.cause === 'race')) tags.push('race:loser');
  return tags;
};

const attemptTags = (I) => [
  `end:${I.att.end.kind}`,
  ...(I.att.n > 0 && I.consumes.some((c) => I.att.journalIn.some((e) => e.idx === c.idx)) ? ['replay'] : []),
  ...cancelTags(I), ...sleepTags(I), ...runTags(I), ...programTags(I),
  ...(I.freeze !== Infinity ? ['freeze'] : []),
  ...(I.consumes.some((c) => c.pos > I.rootExit && c.pos <= I.cut) ? ['closing:wait'] : []),
  ...(I.aborts.some((a) => a.cause === 'deadline') ? ['deadline:fired'] : []),
  ...(compensations(I).size ? ['compensation:send'] : []),
  ...I.violations.map((v) => `violation:${v.kind}`),
];

/** The fold step and the attempt index, shared with the stream monitors. */
export const folding = { foldAttempt, ix };

/** The set of boundary tags a history reaches, for coverage reporting. */
export function boundaries(history) {
  const tags = new Set(history.attempts.flatMap((att) => attemptTags(ix(history, att))));
  if (history.outcome) tags.add(`outcome:${history.outcome.kind}`);
  return tags;
}

/** Claims, or parts of claims, that a history in this format cannot decide. */
export const unjudgeable = [
  { id: 'S2', reason: 'An `issue` event names a journal index, not the command built, so a mismatch is seen only through end.detail "mismatch"; which command differed is not recorded.' },
  { id: 'S5', reason: 'Excluded by the step 7 specification (foreign resumes; a turn is atomic in the model).' },
  { id: 'S6', reason: 'The positive claim (an empty, unawaited state records the blocked violation) is excluded by the step 7 specification. Whether a closure is executing at a trace position needs effect start and settle positions; the predicate uses pending run results instead.' },
  { id: 'S8.P7', reason: 'The second half (L at least the reading at the operation\'s completion) needs the host reading at completion, which the history lacks. Under its hypothesis it follows from P4.' },
  { id: 'S8.P3P9', reason: 'Infinite sleeps are outside the grammar.' },
  { id: 'S14c', reason: 'Excluded by the step 7 specification (Restate retention).' },
  { id: 'S14e', reason: 'Excluded by the step 7 specification (target deduplication).' },
  { id: 'S16b', reason: 'The order in which outcomes are returned to the SDK, and whether each success or terminal failure was proposed before the attempt ended, are not recorded; neither is whether a closure started during the freeze (effects have no positions).' },
  { id: 'S18', reason: 'The positive claim that an Ended cut aborts every executing run is checked only for closures that never settled, since effects have no settle positions.' },
  { id: 'S19', reason: 'Refusal of a deadline not below the inactivity timeout: the configured timeout and the refusal are not in the history.' },
  { id: 'S20', reason: 'Gate liveness (the gate never waits forever) and the gate\'s waiting for consumed causes need effect entry positions.' },
  { id: 'S21', reason: 'Which run\'s retryable failure ended a retried attempt (End has no detail), and whether an escaped compensation failure is included in a cancelled invocation\'s error (Outcome.detail has no fixed form).' },
  { id: 'S22', reason: 'Restate\'s side of each cut (a kill ending children, suspension keeping them) is a premise, not checked.' },
  { id: 'S24', reason: 'Excluded by the step 7 specification (admission).' },
  { id: 'S25', reason: 'The moment the warning becomes due (aborted runs are all that holds the attempt up) needs the full race membership and settle positions; the log when a named run settles is not an event.' },
  { id: 'S26', reason: 'Timing (one inactivity timeout after the later of the abort and the last visible exchange) needs ticks on abort, delivery and flush events and the configured timeout.' },
];

/** Fields the predicates needed and the format lacks. */
export const missingFields = [
  'issue.cmd: the command the executor issued, to name the command that mismatched (S2)',
  'deadline sleep: the run it belongs to; inferred from journal adjacency (S18, S19)',
  'effect: trace position or tick of closure entry and settlement (S6, S16b, S20, S22, S25, S26)',
  'sample: L after it is applied, and each sleep link\'s anchor (P5, P6; bounded from clock reads)',
  'the invocation id (S14b checks one id is shared by every key)',
  'the configured inactivity timeout (S19, S26)',
  'ticks on abort, deliver and issue events (S26)',
  'end.detail: which run\'s retryable failure ended a retried attempt (S16b, S21)',
  'a log event when a run named by the first warning settles (S25)',
  'host reading at each operation\'s completion (P7)',
];
