// Brute-force oracle for the v1 time rule, revision 2 (issue #19).
// Models Restate's journal, host clocks with error, sample retries, operation failures, and a
// crash and replay at every journal index, on a different host. Shares no code with any
// implementation, and none with oracle.mjs. Run: node oracle-v2.mjs  (several minutes)
//
// GRAMMAR AND BOUNDS (fixed before the first run)
// Two phases, so the search stays exhaustive but finite:
//   Phase A: programs of 0 to 2 operations, every live choice below.
//   Phase B: programs of exactly 3 operations, with failed closure executions fixed at 0.
// Operations:
//   R    run that succeeds
//   F    run whose outcome is chosen (ok or declared failure); on failure the handler catches it
//        and sleeps 1 ms before going on
//   C    call that succeeds
//   S1   sleep 1 ms        Sh  sleep 0.5 ms     S0  sleep 0 ms     Sn  sleep -1 ms
//   Si   sleep forever (the program hangs there)
//   SD   sleep until a deadline: d = (L at attempt start + 3) - L, which may be <= 0
// Each durable operation journals a completion entry, then a sample entry (the adopted rule).
// Live choices per sample: host error in {-1, 0, 1}; true time advance before it in {0, 1};
// failed closure executions before success in {0, 1} (phase A only), each costing 1 ms of
// retry delay. Live choice per F outcome: ok or fail. R and C always succeed.
// True time starts at 10. Across a durable sleep it advances by the slept time (ceil(d)).
// Crash and replay: for every journal length k, a new attempt replays the first k entries and
// runs live after that on a different host: error +2, true time 200, and an adversarial clock.
//
// CLAIMS, checked on the original attempt AND on every replay attempt
//   P1 replay: every trace point fixed by the first k journal entries is equal.
//   P2 L never decreases.
//   P3 after a completed durable sleep of d > 0, L grew by at least ceil(d).
//   P4 at each sample point, L >= the sample.
//   P5 L <= true time at that point + the largest error among hosts whose samples were used.
//   P6 L is an integer.
//   P7 after every completed durable operation, whatever its outcome, L >= the host reading
//      at its completion (freshness).
//
// RULE VARIANTS: "adopted" must pass every claim. Each mutant must fail the claim named.
//   noSampleOnFail  skips the sample after a failed run          -> P7
//   negDurable      treats d <= 0 as a durable sleep with floor   -> P2
//   retryLive       re-reads a retried sample live on replay      -> P1
//   replayNoMax     on replayed samples sets L = s (no max)       -> P2 on replay
//   replayAhead     adds 1 to L at replayed samples               -> P5 on replay

const OPS = ["R", "F", "C", "S1", "Sh", "S0", "Sn", "Si", "SD"]
const SLEEP = { S1: 1, Sh: 0.5, S0: 0, Sn: -1, Si: Infinity }
const ERRS = [-1, 0, 1]
const INCS = [0, 1]
const FAILS = [0, 1]
const RETRY_DELAY = 1
const DEADLINE = 3
const REPLAY = { err: 2, start: 200 }

const VARIANTS = {
  adopted: {},
  noSampleOnFail: { noSampleOnFail: true },
  negDurable: { negDurable: true },
  retryLive: { retryLive: true },
  replayNoMax: { replayNoMax: true },
  replayAhead: { replayAhead: true }
}

/** Runs one attempt. `journal` is shared: replayed entries are read, live ones appended. */
const attempt = (v, program, journal, k, live) => {
  const replaying = k !== null
  let t = replaying ? REPLAY.start : 10
  let i = 0, liveN = 0, L, L0, maxErr = -Infinity
  const trace = [], used = [], issues = new Set()
  const point = () => { trace.push(L); used.push(i) }
  const fail = (p) => issues.add(replaying ? `${p}r` : p)

  // A journal entry: replayed if i < k (or i < journal.length on the original), else live.
  const isReplayed = () => replaying ? i < k : false
  const sample = () => {
    if (isReplayed()) {
      const e = journal[i++]
      const retried = e.fails > 0
      if (v.retryLive && retried) {
        const c = live(liveN++, "sample")
        return { s: t + c.err + REPLAY.err, err: c.err + REPLAY.err, tAt: t, hc: t, replayed: true }
      }
      return { ...e, replayed: true }
    }
    const c = live(liveN++, "sample")
    t += c.inc
    const errHere = c.err + (replaying ? REPLAY.err : 0)
    const hc = t + errHere
    t += c.fails * RETRY_DELAY
    const e = { s: t + errHere, err: errHere, tAt: t, hc, fails: c.fails }
    if (replaying) journal.length = i
    journal[i++] = e
    return { ...e, replayed: false }
  }
  const outcome = (chosen) => {
    if (isReplayed()) return journal[i++].ok
    const ok = chosen ? live(liveN++, "outcome").ok : true
    if (replaying) journal.length = i
    journal[i++] = { ok }
    return ok
  }
  const takeSample = (kind, before, slept) => {
    const r = sample()
    maxErr = Math.max(maxErr, r.err)
    let next = kind === "sleep" ? Math.max(before + slept, r.s) : Math.max(before, r.s)
    if (r.replayed && v.replayNoMax) next = r.s
    if (r.replayed && v.replayAhead) next += 1
    L = next
    if (L < before) fail("P2")
    if (kind === "sleep" && slept > 0 && L < before + slept) fail("P3")
    if (L < r.s) fail("P4")
    if (L > r.tAt + maxErr) fail("P5")
    if (!Number.isInteger(L)) fail("P6")
    if (L < r.hc) fail("P7")
    point()
  }
  const sleep = (d) => {
    if (d === Infinity) { trace.push("HANG"); used.push(i); return false }
    if (d <= 0 && !v.negDurable) { point(); return true }
    const slept = Math.ceil(d)
    const before = L
    if (!isReplayed()) { t += Math.max(slept, 0); if (replaying) journal.length = i; journal[i++] = { sleep: slept } } else i++
    takeSample("sleep", before, slept)
    return true
  }

  // Attempt start.
  const r0 = sample()
  maxErr = r0.err
  L = r0.s
  L0 = L
  if (r0.replayed && v.replayAhead) L += 1
  if (L > r0.tAt + maxErr) fail("P5")
  point()
  for (const op of program) {
    if (op === "R" || op === "C") { outcome(false); takeSample("op", L, 0); continue }
    if (op === "F") {
      const ok = outcome(true)
      if (ok || !v.noSampleOnFail) takeSample("op", L, 0)
      else {
        // Freshness check without a sample: the host reading at completion.
        const hc = t + (replaying ? REPLAY.err : 0)
        if (L < hc) fail("P7")
        point()
      }
      if (!ok && !sleep(1)) break
      continue
    }
    const d = op === "SD" ? L0 + DEADLINE - L : SLEEP[op]
    if (!sleep(d)) break
  }
  return { trace, used, issues }
}

function* programs(min, max) {
  for (let n = min; n <= max; n++) {
    const idx = new Array(n).fill(0)
    while (true) {
      yield idx.map((j) => OPS[j])
      let p = n - 1
      while (p >= 0 && ++idx[p] === OPS.length) idx[p--] = 0
      if (p < 0) break
    }
  }
}

/** Choices for one live slot, by kind. Each slot enumerates only its own kind. */
const slotChoices = (kind, fails) => kind === "outcome"
  ? [{ ok: true }, { ok: false }]
  : ERRS.flatMap((err) => INCS.flatMap((inc) => fails.map((f) => ({ err, inc, fails: f }))))

/** Every live-choice sequence for a program, explored depth first. */
const explore = (v, program, fails, onRun) => {
  const recurse = (prefix) => {
    const journal = []
    let nextKind = null
    const live = (n, kind) => {
      if (n < prefix.length) return prefix[n]
      nextKind ??= kind
      return kind === "outcome" ? { ok: true } : { err: 0, inc: 0, fails: 0 }
    }
    const result = attempt(v, program, journal, null, live)
    if (nextKind === null) return onRun(result, journal)
    for (const c of slotChoices(nextKind, fails)) recurse([...prefix, c])
  }
  recurse([])
}

const adversary = (n, kind) => kind === "outcome" ? { ok: n % 2 === 0 } : { err: 7 - 5 * n, inc: 3, fails: n % 2 }

const results = {}
for (const [name, v] of Object.entries(VARIANTS)) {
  const counts = { runs: 0, replays: 0 }
  const first = {}
  const phases = [[0, 2, FAILS], [3, 3, [0]]]
  for (const [min, max, fails] of phases) for (const program of programs(min, max)) {
    explore(v, program, fails, (original, journal) => {
      counts.runs++
      for (const p of original.issues) { counts[p] = (counts[p] ?? 0) + 1; first[p] ??= { program, trace: original.trace } }
      for (let k = 0; k <= journal.length; k++) {
        counts.replays++
        const copy = journal.slice()
        const replay = attempt(v, program, copy, k, adversary)
        for (const p of replay.issues) { counts[p] = (counts[p] ?? 0) + 1; first[p] ??= { program, k, trace: replay.trace } }
        const same = original.trace.every((x, j) => original.used[j] > k || x === replay.trace[j])
        if (!same) { counts.P1 = (counts.P1 ?? 0) + 1; first.P1 ??= { program, k, original: original.trace, replay: replay.trace } }
      }
    })
  }
  results[name] = { counts, first }
  console.log(`== ${name}: ${JSON.stringify(counts)}`)
  for (const [p, e] of Object.entries(first)) console.log(`   first ${p}: ${JSON.stringify(e)}`)
}
