// Restate journals Sleep.wake_up_time = host Date.now() + millis (computed in the SDK), and the
// server fires it by its own clock. So true slept time = max(0, d + eHostAtCmd - eServer).
// Model: one sample at start, then one sleep (asked ceil(d)), then the post-sleep sample.
// Rule (adopted): L' = max(L + ceil(d), s). Check P3 (growth >= true slept) and P5 (L <= t + maxErr).
const errs = [-1000, 0, 1000]
let p3 = null, p5 = null, p5HostAccurate = null, p2neg = null
for (const e0 of errs) for (const eCmd of errs) for (const eSrv of errs) for (const e1 of errs) for (const d of [500, 2000]) {
  let t = 10_000
  const s0 = t + e0; let L = s0
  t += 0 // sleep command issued right after the sample
  const wake = t + eCmd + d            // host-frame absolute wake time
  const tFire = Math.max(t, wake - eSrv) // server fires when its clock >= wake
  const slept = tFire - t
  t = tFire
  const s1 = t + e1
  const before = L
  L = Math.max(L + Math.ceil(d), s1)
  const maxErr = Math.max(e0, e1) // all host errors seen at sample points in the attempt
  const ex = { e0, eCmd, eSrv, e1, d, slept, before, L, trueT: t, host: s1 }
  if (L - before < slept && !p3) p3 = ex
  if (L > t + maxErr && !p5) p5 = ex
  if (L > t + maxErr && e0 === 0 && eCmd === 0 && e1 === 0 && !p5HostAccurate) p5HostAccurate = ex
}
// Negative durations: Effect allows Duration.millis(-5); the rule as written would apply L + ceil(-5).
{ const L = 10_000, s = 9_990; const next = Math.max(L + Math.ceil(-5), s); if (next < L) p2neg = { L, s, d: -5, next } }
console.log("P3 (growth >= real slept) counterexample:", JSON.stringify(p3))
console.log("P5 counterexample:", JSON.stringify(p5))
console.log("P5 counterexample with an accurate SDK host (server clock skew only):", JSON.stringify(p5HostAccurate))
console.log("P2 with negative duration applied literally:", JSON.stringify(p2neg))
