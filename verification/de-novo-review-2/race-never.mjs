// After a swallowed guard violation, the sticky rule acts only at the next durable operation or
// at handler exit. If the surviving race branch never ends, neither happens.
import { Effect } from "../../spike/node_modules/effect/dist/index.js"
const violation = Effect.die("guard: two durable operations pending")
const handler = Effect.race(Effect.never, violation)
const r = await Promise.race([
  Effect.runPromiseExit(handler).then((e) => "handler exited: " + e._tag),
  new Promise((res) => setTimeout(() => res("still running after 500 ms: no exit, so no sticky defect"), 500))
])
console.log(r)
process.exit(0)
