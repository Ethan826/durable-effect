// Brute-force oracle for the logical-time rule of the durable-effect v1 design.
// It models Restate's journal, a host clock with error, and a crash at every journal index.
// It shares no code with any implementation. Run: node oracle.mjs
//
// GRAMMAR AND BOUNDS (fixed before the first run):
// - Program: a sequence of 0..4 ops, each one of R (run), C (call), S1, S2 (sleep 1 or 2 ms),
//   Sh (sleep 0.5 ms, the fractional case).
// - True time starts at 10. Between consecutive samples it advances by inc in {0,1}; across a
//   sleep of requested d it advances by trunc(d) + inc, since Restate sleeps trunc(d).
// - The host clock reads true time + err, err in {-1,0,1}, chosen per sample.
// - Crash: after the original attempt, for every journal length k, a new attempt replays the
//   first k entries and runs live after that with an adversarial host clock (900 - i).
//
// CLAIMS checked per rule variant:
//   P1 replay: L at every journaled point of the replayed prefix equals the original's.
//   P2 monotone: L never decreases within an attempt.
//   P3 floor: after a sleep, L grows by at least the duration Restate actually slept.
//   P4 lower: at every sample point, L >= the host reading taken there.
//   P5 upper: L <= true time + the largest host error seen so far in the attempt.
//   P6 integer: L is always an integer number of milliseconds.
//   P7 design text "L runs ahead of the host clock by at most the size of the backward step":
//      checked as L - host <= the largest single backward step seen so far.

const ops = ["R", "C", "S1", "S2", "Sh"]
const requested = { S1: 1, S2: 2, Sh: 0.5 }
const errs = [-1, 0, 1]
const incs = [0, 1]

/** Rule variants. Each returns the events that sample, and the next L for an event. */
const variants = {
  // The design as drafted: + requested d.
  draftA: { sampleAfter: () => true, sleepAdd: (d) => d, next },
  // The fix: + the ceiling of d, and Restate is asked to sleep ceil(d).
  fixedA: { sampleAfter: () => true, sleepAdd: Math.ceil, asked: Math.ceil, next },
  // Approach C: no sample after run or call.
  approachC: { sampleAfter: (op) => op.startsWith("S"), sleepAdd: Math.ceil, asked: Math.ceil, next },
  // Must fail: no floor after sleep.
  noFloor: { sampleAfter: () => true, sleepAdd: () => 0, asked: Math.ceil, next },
  // Must fail: reads the live host clock instead of the journaled one.
  liveRead: { sampleAfter: () => true, sleepAdd: Math.ceil, asked: Math.ceil, next, live: true }
}
function next(L, kind, s, add) {
  if (kind === "start") return s
  if (kind === "sleep") return Math.max(L + add, s)
  return Math.max(L, s)
}

function* programs(maxLen) {
  for (let n = 0; n <= maxLen; n++) {
    const idx = new Array(n).fill(0)
    while (true) {
      yield idx.map((i) => ops[i])
      let p = n - 1
      while (p >= 0 && ++idx[p] === ops.length) idx[p--] = 0
      if (p < 0) break
    }
  }
}
function* choices(count) {
  const total = (errs.length * incs.length) ** count
  for (let c = 0; c < total; c++) {
    let x = c
    const out = []
    for (let i = 0; i < count; i++) {
      out.push({ err: errs[x % 3], inc: incs[Math.floor(x / 3) % 2] })
      x = Math.floor(x / 6)
    }
    yield out
  }
}

/** One attempt. `journal` holds recorded samples; entries past it are live. Returns L trace. */
function attempt(variant, program, journal, live) {
  const asked = variant.asked ?? Math.trunc
  let t = 10, i = 0, L, maxErr = -Infinity, maxBack = 0, prevHost
  const trace = [], used = [], issues = []
  const record = (v) => { trace.push(v); used.push(i) }
  const sample = (advance) => {
    t += advance
    const c = live(i)
    const host = t + c.err
    if (prevHost !== undefined && host < prevHost) maxBack = Math.max(maxBack, prevHost - host)
    prevHost = host
    maxErr = Math.max(maxErr, c.err)
    const s = i < journal.length ? journal[i] : host
    if (i >= journal.length) journal.push(s)
    i++
    return { s, host, replayed: i <= journal.length }
  }
  const check = (event, before, host, slept) => {
    if (before !== undefined && L < before) issues.push("P2")
    if (event === "sleep" && L < before + slept) issues.push("P3")
    if (L < host) issues.push("P4")
    if (L > t + maxErr) issues.push("P5")
    if (!Number.isInteger(L)) issues.push("P6")
    if (L - host > maxBack) issues.push("P7")
  }
  const first = sample(live(0).inc)
  L = first.s
  record(variant.live ? first.host : L)
  check("start", undefined, first.host, 0)
  for (const op of program) {
    const isSleep = op.startsWith("S")
    const slept = isSleep ? asked(requested[op]) : 0
    const before = L
    if (variant.sampleAfter(op)) {
      const { s, host } = sample(slept + live(i).inc)
      L = next(L, isSleep ? "sleep" : "op", s, isSleep ? variant.sleepAdd(requested[op]) : 0)
      record(variant.live ? host : L)
      check(isSleep ? "sleep" : "op", before, host, slept)
    } else {
      t += slept + live(i).inc
      record(variant.live ? t : L)
    }
  }
  return { trace, used, issues }
}

const results = {}
for (const [name, variant] of Object.entries(variants)) {
  const counts = { runs: 0, P1: 0, P2: 0, P3: 0, P4: 0, P5: 0, P6: 0, P7: 0 }
  const examples = {}
  for (const program of programs(4)) {
    const samples = 1 + program.length
    for (const choice of choices(samples)) {
      const journal = []
      const original = attempt(variant, program, journal, (k) => choice[k] ?? { err: 0, inc: 0 })
      counts.runs++
      for (const p of new Set(original.issues)) {
        counts[p]++
        examples[p] ??= { program, choice, trace: original.trace }
      }
      for (let k = 0; k <= journal.length; k++) {
        const replay = attempt(variant, program, journal.slice(0, k), (n) => ({ err: 500 - 7 * n, inc: 3 }))
        // Adversarial live clock for unpersisted entries: very different readings.
        // Compare every trace point determined only by the first k journal entries.
        const same = original.trace.every((v, j) => original.used[j] > k || v === replay.trace[j])
        if (!same) {
          counts.P1++
          examples.P1 ??= { program, k, original: original.trace, replay: replay.trace }
        }
      }
    }
  }
  results[name] = { counts, examples }
}
for (const [name, { counts, examples }] of Object.entries(results)) {
  console.log(`\n== ${name}: ${JSON.stringify(counts)}`)
  for (const [p, e] of Object.entries(examples)) console.log(`  first ${p} counterexample: ${JSON.stringify(e)}`)
}
