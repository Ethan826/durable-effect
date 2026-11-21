// E3 says a forked fiber starts as a task on its parent's dispatcher. Count the tasks queued
// and the order of steps for Effect.forkChild versus concurrent Effect.all.
import { Effect, Scheduler } from "../../spike/node_modules/effect/dist/index.js"
const log = []
let tasks = 0
const queue = []
const dispatcher = { scheduleTask: (t) => { tasks++; queue.push(t); setImmediate(() => { while (queue.length) queue.shift()() }) }, flush: () => {} }
const scheduler = { executionMode: "async", makeDispatcher: () => dispatcher, shouldYield: () => false }
const step = (s) => Effect.sync(() => log.push(s))
const viaFork = Effect.gen(function* () {
  yield* Effect.forkChild(step("child"))
  yield* step("parent after fork")
  yield* Effect.yieldNow
})
const viaAll = Effect.gen(function* () {
  yield* Effect.all([step("a"), step("b")], { concurrency: 2 })
  yield* step("parent after all")
})
for (const [name, eff] of [["forkChild", viaFork], ["Effect.all concurrency 2", viaAll]]) {
  log.length = 0; tasks = 0
  await Effect.runPromise(eff, { scheduler })
  console.log(`${name}: tasks queued=${tasks}, order=${JSON.stringify(log)}`)
}
