// The sleep row admits 0 < d <= 2^53 - 1 ms and sets L to max(L + ceil(d), s). With L near the
// current epoch (~1.8e12 ms), L + ceil(d) exceeds 2^53 and IEEE addition rounds it. Check P3
// (L grows by at least ceil(d)) and P6 (L whole) for d at and near the bound.
const L = 1_795_000_000_001 // an odd epoch millisecond in late 2026
for (const d of [2 ** 53 - 1, 2 ** 53 - 2, 2 ** 53 - 1 - L, 2 ** 53 - L, 2 ** 52 + 1]) {
  const next = Math.max(L + Math.ceil(d), L) // s is far smaller than L + d
  const grown = BigInt(next) - BigInt(L)
  const ok = grown >= BigInt(Math.ceil(d))
  console.log(`d=${d} next=${next} grown=${grown} ceil(d)=${BigInt(Math.ceil(d))} P3=${ok ? "holds" : "FAILS"} safe=${Number.isSafeInteger(next)}`)
}
// Search for a d at or below the bound where rounding goes down.
let found = 0
for (let L2 = 1_795_000_000_000; L2 < 1_795_000_000_010 && found < 3; L2++) {
  for (let d = 2 ** 53 - 1; d > 2 ** 53 - 12 && found < 3; d--) {
    const grown = BigInt(L2 + d) - BigInt(L2)
    if (grown < BigInt(d)) { found++; console.log(`DOWN: L=${L2} d=${d} L+ceil(d)=${L2 + d} grown=${grown} < ${d}: P3 FAILS; next L whole=${Number.isInteger(L2 + d)} safe=${Number.isSafeInteger(L2 + d)}`) }
  }
}
// What the nanosecond readers return for such an L.
const Lb = 1_795_000_000_001 + (2 ** 53 - 2)
console.log("nanos of rounded L:", BigInt(Lb) * 1000000n, " Date(L) valid:", !Number.isNaN(new Date(Lb).getTime()))
