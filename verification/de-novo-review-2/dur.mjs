// Probes Duration edge values in effect 4.1.5 and what Clock.sleep would receive.
import { Duration, Effect } from "../../spike/node_modules/effect/dist/index.js"
const show = (label, f) => { try { const d = f(); console.log(label, String(d), "toMillis=", Duration.toMillis(d)) } catch (e) { console.log(label, "THROWS", e.message) } }
show("millis(-1)", () => Duration.millis(-1))
show("fromInputUnsafe(-5)", () => Duration.fromInputUnsafe(-5))
show("fromInputUnsafe(NaN)", () => Duration.fromInputUnsafe(NaN))
show("millis(NaN)", () => Duration.millis(NaN))
show("nanos(-1n)", () => Duration.nanos(-1n))
show("nanos(1n)", () => Duration.nanos(1n))
show("'-1 millis'", () => Duration.fromInputUnsafe("-1 millis"))
show("infinity", () => Duration.infinity)
show("negativeInfinity?", () => Duration.fromInputUnsafe(-Infinity))
show("millis(1e20)", () => Duration.millis(1e20))
show("subtract(1ms,2ms)", () => Duration.subtract(Duration.millis(1), Duration.millis(2)))
