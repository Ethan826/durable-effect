// Probes for the statement review of the scheduling dossier (E1, S5, S1).
// A minimal stand-in for the design's DeterministicScheduler: one shared dispatcher per
// executor, turns that drain the queue synchronously, and shouldYield that records a
// violation when called outside this executor's turn (rule 4).
import { Effect, Fiber, Ref, Scheduler, References, Semaphore } from "../../spike/node_modules/effect/dist/index.js"

const makeExecutor = (name, globalTurn) => {
  const ex = { name, inTurn: false, violations: [], queue: [], scheduled: false }
  const runTurn = () => {
    ex.scheduled = false
    ex.inTurn = true; if (globalTurn) globalTurn.depth++
    while (ex.queue.length > 0) ex.queue.shift()()
    ex.inTurn = false; if (globalTurn) globalTurn.depth--
  }
  const dispatcher = {
    scheduleTask: (task) => { ex.queue.push(task); if (!ex.scheduled) { ex.scheduled = true; setImmediate(runTurn) } },
    flush: () => runTurn()
  }
  ex.scheduler = {
    executionMode: "async",
    makeDispatcher: () => dispatcher,
    shouldYield: (fiber) => {
      const ok = globalTurn ? globalTurn.depth > 0 : ex.inTurn
      if (!ok) ex.violations.push(`step outside turn (fiber ${fiber.id})`)
      return fiber.currentOpCount >= 2048
    }
  }
  return ex
}
// The root fiber starts inside a turn, as the executor would start it.
const run = (ex, eff) => new Promise((resolve) => ex.scheduler.makeDispatcher().scheduleTask(() =>
  resolve(Effect.runPromiseExit(eff, { scheduler: ex.scheduler }))))
const foreignWait = (ms, v) => Effect.callback((resume) => { setTimeout(() => resume(Effect.succeed(v)), ms) })

// Scenario A: a foreign timer resume, with and without PreventSchedulerYield.
for (const prevent of [false, true]) {
  const ex = makeExecutor("A")
  const body = Effect.gen(function* () {
    const v = yield* foreignWait(5, 42)
    // a step whose effect the trace would show (a clock read, a draw, a command)
    yield* Effect.sync(() => ex.seen = `step ran with inTurn=${ex.inTurn}, violations recorded before it=${ex.violations.length}`)
    return v + 1
  })
  const eff = prevent ? body.pipe(Effect.provideService(References.PreventSchedulerYield, true)) : body
  const exit = await run(ex, eff)
  console.log(`A PreventSchedulerYield=${prevent}: exit=${exit._tag} value=${exit.value} violations=${JSON.stringify(ex.violations)}; ${ex.seen}`)
}

// Scenario B: a Ref written by a fiber outside the handler (as a run action's closure would,
// on Effect's default scheduler, live only) and read by a handler fiber in its turns.
for (const actionDelay of [1, 30]) {
  const ex = makeExecutor("B")
  const eff = Effect.gen(function* () {
    const ref = yield* Ref.make(0)
    // stand-in for run(Ref.set(ref, 1)): a separate root on the default scheduler
    yield* Effect.sync(() => setTimeout(() => Effect.runFork(Ref.set(ref, 1)), actionDelay))
    // stand-in for awaiting a durable sleep delivered at a turn boundary after 10 ms
    yield* Effect.callback((resume) => { setTimeout(() => ex.scheduler.makeDispatcher().scheduleTask(() => resume(Effect.void)), 10) })
    return yield* Ref.get(ref)
  })
  const exit = await run(ex, eff)
  console.log(`B action at ${actionDelay} ms: handler read ${exit.value}, violations=${JSON.stringify(ex.violations)}`)
}

// Scenario C: a semaphore shared by two invocations (a service built once in the runtime).
// X releases it inside X's turn; Y's waiting fiber resumes nested inside X's turn.
for (const global of [false, true]) {
  const g = global ? { depth: 0 } : undefined
  const X = makeExecutor("X", g), Y = makeExecutor("Y", g)
  const sem = await Effect.runPromise(Semaphore.make(1))
  const xEff = Effect.gen(function* () {
    yield* sem.take(1)
    yield* foreignWait(10, 0).pipe(Effect.andThen(Effect.yieldNow)) // stand-in: X's work spans a delivery
    yield* sem.release(1)
  })
  const yEff = Effect.gen(function* () { yield* Effect.yieldNow; yield* sem.take(1); return "y" })
  await Promise.all([run(X, xEff), run(Y, yEff)])
  console.log(`C turn flag ${global ? "global" : "per executor"}: Y violations=${JSON.stringify(Y.violations.filter((v) => true))}`)
}
