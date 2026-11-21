// Brute-force oracle for the v1 time rule, revision 3 (issue #23).
// Models Restate's journal, host clocks with error, operation failures, cancellation, very long
// sleeps, sample retries, and a crash and replay at every journal index on two other hosts.
// Written from scratch; it shares no code with oracle.mjs or oracle-v2.mjs, nor with any
// implementation. Run: node oracle-v3.mjs  (several minutes)
//
// GRAMMAR AND BOUNDS (fixed before the first run)
// Operations:
//   R     run that succeeds              F   run whose outcome is chosen: ok or declared failure
//   C     call that succeeds             G   call whose outcome is chosen: ok or terminal failure
//         After a failed F or G the handler catches the failure and sleeps 1 ms.
//   S1    sleep 1 ms                     S5  sleep 5 ms
//   S0    sleep 0 ms                     SB  sleep 2^64 + 4096 ms (above 2^53 - 1: never completes)
// Cancellation: one choice per run, cancelAt in {none, 0, ..., n-1}. The operation at that index
// is cancelled before it completes. A cancelled sleep is cancelled 1 ms after it starts. The
// handler then runs one compensating R and ends. The SDK reports a cancel once (fixture, #20).
// Each durable operation journals one entry (completion or cancel), then one sample entry.
// Live choices per sample: host error, true-time advance between completion and sample in {0,1},
// and failed closure executions before success, each costing 1 ms.
//   Phase A: programs of 0 to 2 operations; error in {-1,0,1}, advance {0,1}, failures {0,1}.
//   Phase B: programs of exactly 3 operations; error in {-1,1}, advance {0,1}, failures {0}.
// Outcome choices for F and G: ok or fail. True time starts at 10. Across a completed sleep it
// advances by the slept time.
// Replays: for every journal length k, a new attempt replays the first k entries, then runs live
// with an adversarial clock on one of two hosts: error +2 from true time 200, or error -3 from
// true time 60. Every original run ends before true time 60.
//
// CLAIMS, checked on originals and on every replay
//   P1 replay: every trace point fixed by the first k journal entries is equal.
//   P2 L never decreases.
//   P3 after a completed sleep of d > 0, L grew by at least ceil(d).
//   P4 at each sample point, L >= the sample.
//   P5 L <= true time at that point + the largest error among hosts whose samples were used.
//   P6 L is an integer.
//   P7 after every durable operation that completes, fails or is cancelled, L >= the host
//      reading at that moment, measured at completion, separately from the sample.
//   P9 a sleep above 2^53 - 1 ms never completes: nothing after it runs.
//
// ASSERTIONS (gate-integrity standard block). The run exits non-zero unless:
//   - the adopted rule fails no claim;
//   - each mutant fails the claim named below (the symptom of its defect);
//   - the adopted rule's run and replay counts equal the pinned denominators, and the scan
//     includes the named member: program ["S5"] cancelled at index 0.
// Checker mutant: CHECKER_MUTANT=P5 disables the P5 check, and the run must then exit non-zero
// because floorOnCancel no longer fails P5. ONLY=<variant> runs one variant, for that check.
//
// RULE VARIANTS: "adopted" must pass every claim. Each mutant must fail the claim named.
//   floorOnCancel     adds ceil(d) to L after a cancelled sleep          -> P5
//   noSampleOnCancel  takes no sample after a cancelled operation        -> P7
//   noSampleOnCallFail takes no sample after a failed call               -> P7
//   hugeToRestate     sends a huge sleep to Restate, which wraps it mod 2^64 to 4096 ms -> P9
//   replayAhead       adds 1 to L at replayed samples                    -> P5 on replay, P1

const OPS = ["R", "F", "C", "G", "S1", "S5", "S0", "SB"]
const SLEEP = { S1: 1, S5: 5, S0: 0, SB: 2 ** 64 + 4096 }
const MAX_SLEEP = 2 ** 53 - 1
const WRAP = 2n ** 64n
const RETRY_DELAY = 1
const CANCEL_AFTER = 1
const HOSTS = [{ err: 2, start: 200 }, { err: -3, start: 60 }]
const PHASES = [
  { min: 0, max: 2, errs: [-1, 0, 1], incs: [0, 1], fails: [0, 1] },
  { min: 3, max: 3, errs: [-1, 1], incs: [0, 1], fails: [0] }
]
const VARIANTS = {
  adopted: {},
  floorOnCancel: { floorOnCancel: true },
  noSampleOnCancel: { noSampleOnCancel: true },
  noSampleOnCallFail: { noSampleOnCallFail: true },
  hugeToRestate: { hugeToRestate: true },
  replayAhead: { replayAhead: true }
}

/** The claim each variant must fail; [] means it must fail none. */
const EXPECTED = {
  adopted: [], floorOnCancel: ["P5"], noSampleOnCancel: ["P7"],
  noSampleOnCallFail: ["P7"], hugeToRestate: ["P9"], replayAhead: ["P5r"]
}
/** Pinned denominators from the first run (2026-11-21), for the adopted rule. */
const PINNED = { runs: 7682052, replays: 153535760 }
const DISABLED = process.env.CHECKER_MUTANT
const ONLY = process.env.ONLY

const isSleep = (op) => op in SLEEP
const isDurable = (op) => !isSleep(op) || (SLEEP[op] > 0 && SLEEP[op] <= MAX_SLEEP)

/** One attempt. `host` is null for the original. Returns the trace of L and the issues found. */
const attempt = (v, program, cancelAt, journal, k, host, live) => {
  const replaying = host !== null
  const hostErr = replaying ? host.err : 0
  let t = replaying ? host.start : 10
  let i = 0, slot = 0, L, maxErr = -Infinity
  const trace = [], used = [], issues = new Set()
  const fail = (p) => { if (p !== DISABLED) issues.add(replaying ? `${p}r` : p) }
  const point = (x = L) => { trace.push(x); used.push(i) }
  const replayed = () => replaying && i < k
  const append = (e) => { journal.length = i; journal[i++] = e }

  // A sample: replayed from the journal, or live from this host.
  const sample = () => {
    if (replayed()) return { ...journal[i++], fromJournal: true }
    const c = live(slot++, "sample")
    const err = c.err + hostErr
    const hc = t + err                       // host reading at completion, before the advance
    t += c.inc + c.fails * RETRY_DELAY
    const e = { kind: "sample", s: t + err, err, tAt: t, hc }
    append(e)
    return { ...e, fromJournal: false }
  }
  // The entry before the sample: a completion, a failure or a cancel.
  const event = (entry) => {
    if (replayed()) return journal[i++]
    append(entry)
    return entry
  }
  const choose = () => replayed() ? journal[i].ok : live(slot++, "outcome").ok
  const check = (before, r, floor) => {
    maxErr = Math.max(maxErr, r.err)
    if (L < before) fail("P2")
    if (floor > 0 && L < before + floor) fail("P3")
    if (L < r.s) fail("P4")
    if (L > r.tAt + maxErr) fail("P5")
    if (!Number.isInteger(L)) fail("P6")
    if (L < r.hc) fail("P7")
  }
  const afterOp = (floor) => {
    const before = L
    const r = sample()
    L = Math.max(before + floor, r.s)
    if (r.fromJournal && v.replayAhead) L += 1
    check(before, r, floor)
    point()
  }
  // No sample (a mutant): P7 against the host reading at this moment.
  const skipSample = () => { if (L < t + hostErr) fail("P7"); point() }

  const sleep = (d) => {
    if (d <= 0) { point(); return true }
    let wait = d
    if (d > MAX_SLEEP) {
      if (!v.hugeToRestate) { trace.push("HANG"); used.push(i); return false }
      fail("P9")
      wait = Number(BigInt(d) % WRAP)
    }
    const slept = Math.ceil(wait)
    if (!replayed()) t += slept
    event({ kind: "slept", slept })
    afterOp(slept)
    return true
  }
  const cancel = (op) => {
    if (!replayed()) t += isSleep(op) ? CANCEL_AFTER : 0
    event({ kind: "cancel" })
    if (v.noSampleOnCancel) skipSample()
    else {
      const floor = v.floorOnCancel && isSleep(op) ? Math.ceil(SLEEP[op]) : 0
      afterOp(floor)
    }
    event({ kind: "done" })                  // the compensating run
    afterOp(0)
  }

  // Attempt start.
  const r0 = sample()
  L = r0.s
  if (r0.fromJournal && v.replayAhead) L += 1
  maxErr = r0.err
  if (L > r0.tAt + maxErr) fail("P5")
  point()
  for (let n = 0; n < program.length; n++) {
    const op = program[n]
    if (n === cancelAt && isDurable(op)) { cancel(op); break }
    if (isSleep(op)) { if (!sleep(SLEEP[op])) break; continue }
    const chosen = op === "F" || op === "G"
    const ok = chosen ? choose() : true
    event({ kind: "outcome", ok })
    if (!ok && op === "G" && v.noSampleOnCallFail) skipSample()
    else afterOp(0)
    if (!ok && !sleep(1)) break
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

const choicesFor = (kind, phase) => kind === "outcome"
  ? [{ ok: true }, { ok: false }]
  : phase.errs.flatMap((err) => phase.incs.flatMap((inc) =>
      phase.fails.map((fails) => ({ err, inc, fails }))))

/** Every live-choice sequence for one program and cancel point, explored depth first. */
const explore = (v, program, cancelAt, phase, onRun) => {
  const recurse = (prefix) => {
    const journal = []
    let pending = null
    const live = (n, kind) => {
      if (n < prefix.length) return prefix[n]
      pending ??= kind
      return kind === "outcome" ? { ok: true } : { err: 0, inc: 0, fails: 0 }
    }
    const result = attempt(v, program, cancelAt, journal, null, null, live)
    if (pending === null) return onRun(result, journal)
    for (const c of choicesFor(pending, phase)) recurse([...prefix, c])
  }
  recurse([])
}

const adversary = (n, kind) => kind === "outcome"
  ? { ok: n % 2 === 1 }
  : { err: 5 - 4 * n, inc: 2, fails: n % 2 }

const problems = []
for (const [name, v] of Object.entries(VARIANTS)) {
  if (ONLY && name !== ONLY) continue
  const counts = { runs: 0, replays: 0 }
  const first = {}
  let namedMember = false
  const note = (p, e) => { counts[p] = (counts[p] ?? 0) + 1; first[p] ??= e }
  for (const phase of PHASES) for (const program of programs(phase.min, phase.max)) {
    for (let cancelAt = -1; cancelAt < program.length; cancelAt++) {
      explore(v, program, cancelAt, phase, (original, journal) => {
        counts.runs++
        if (program.length === 1 && program[0] === "S5" && cancelAt === 0) namedMember = true
        for (const p of original.issues) note(p, { program, cancelAt, trace: original.trace })
        for (const host of HOSTS) for (let k = 0; k <= journal.length; k++) {
          counts.replays++
          const replay = attempt(v, program, cancelAt, journal.slice(), k, host, adversary)
          for (const p of replay.issues) note(p, { program, cancelAt, k, host, trace: replay.trace })
          const same = original.trace.every((x, j) => original.used[j] > k || x === replay.trace[j])
          if (!same) note("P1", { program, cancelAt, k, host, original: original.trace, replay: replay.trace })
        }
      })
    }
  }
  console.log(`== ${name}: ${JSON.stringify(counts)}`)
  for (const [p, e] of Object.entries(first)) console.log(`   first ${p}: ${JSON.stringify(e)}`)
  const failed = Object.keys(counts).filter((key) => key !== "runs" && key !== "replays")
  const expected = EXPECTED[name]
  if (expected.length === 0 && failed.length > 0) problems.push(`${name} failed ${failed.join(", ")}`)
  for (const claim of expected) if (!counts[claim]) problems.push(`${name} did not fail ${claim}`)
  if (name === "adopted" && (counts.runs !== PINNED.runs || counts.replays !== PINNED.replays)) {
    problems.push(`adopted scanned ${counts.runs} runs and ${counts.replays} replays, pinned ${PINNED.runs} and ${PINNED.replays}`)
  }
  if (!namedMember) problems.push(`${name} never explored the named member ["S5"] cancelled at 0`)
}
if (problems.length > 0) {
  console.log("FAIL"); for (const problem of problems) console.log(`  ${problem}`)
  process.exitCode = 1
} else console.log("PASS")
