import { Duration } from "../../spike/node_modules/effect/dist/index.js"
for (const d of [Duration.millis(-5), Duration.millis(0.4), Duration.nanos(1n), Duration.infinity, Duration.fromInputUnsafe("-3 millis")]) {
  try { console.log(String(d), Duration.toMillis(d), Math.ceil(Duration.toMillis(d))) } catch (e) { console.log("throws", e.message) }
}
