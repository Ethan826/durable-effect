# The history interface

Revised 2026-11-24 after the first joint run: `release` events, a turn's cause index,
`entered: null`, the retryable root exit and the mismatch detail. Revised again: closure lifecycle
events, `done`, entry and command contents on `consume` and `issue`, and the event stream.

The step 7 check (#48, comment 7144185705) has three parts that import nothing from one another:
the environment model, the executor model, and the predicates. The first two together produce one
history per program and schedule. The predicates read only the history. This file fixes its shape.
A history is plain JSON data.

## Program

`history.program` is the handler as written, which an observer may read.

```
Program  = { fibers: Fiber[] }             // fibers[0] is the root
Fiber    = { id: "f0" | "f1", daemon: boolean, body: Stmt[] }
Stmt     =
  | { s: "run",   op: OpName, behaviour: Behaviour, deadline?: 1 | 2 }
  | { s: "sleep", op: OpName, ms: 0 | 1 | 2 | 3 }
  | { s: "call",  op: OpName, result: "ok" | "terminal" }
  | { s: "await", op: OpName }
  | { s: "race",  ops: [OpName, OpName] }  // the loser's operation is released
  | { s: "fork",  fiber: "f1" }
  | { s: "uninterruptible", body: Stmt[] }
  | { s: "ensuring", body: Stmt[], finalizer: Stmt[] }
  | { s: "clock" } | { s: "draw" }
  | { s: "return" } | { s: "fail", kind: "terminal" | "retryable" }
OpName    = string                         // unique per program text, e.g. "r1", "s1", "c1"
Behaviour = "ok" | "terminal" | "retryable" | "honour" | "ignoreOk" | "ignoreRetryable" | "mapAbort"
```

Behaviours: `honour` settles with the abort as soon as its signal is aborted and otherwise
succeeds; `ignoreOk` and `ignoreRetryable` ignore the signal; `mapAbort` rejects with an error of
its own when aborted and otherwise succeeds.

## Invocation

```
History = {
  program: Program,
  attempts: Attempt[],              // in order; the last one ends the invocation or the bound
  outcome: Outcome | null,          // the invocation's final outcome, null if no attempt decided one
  children: Child[],                // child invocations, across attempts
}
Outcome = { kind: "success" | "terminal" | "cancelled" | "defect", detail?: string }
// A root that fails retryably reports kind "retryable" in its rootExit event only;
// its attempt ends "retry" and no Output is written.
```

## Attempt

```
Attempt = {
  n: number,                        // 0, 1, ...
  journalIn: Entry[],               // the persisted journal when the attempt starts (its replay prefix)
  journalOut: Entry[],              // the persisted journal when it ends; journalIn is a prefix of it
  trace: Event[],                   // what handler code and outside observers saw, in order
  effects: Effect[],                // one entry per closure execution in this attempt
  end: End,
}
End = { kind: "output" | "suspended" | "ended" | "crashed" | "killed" | "retry",
        at: number,                  // index in trace after which the attempt ended
        detail?: "mismatch" }        // a replay that issued a different command
```

`retry` is an attempt ended by a retryable failure the executor returned to the SDK (the freeze,
§7.4). `ended` is Restate's abort timeout. `output` is an attempt that wrote Output.

## Journal entries

```
Entry =
  | { e: "cmd",    idx: number, cmd: Cmd }
  | { e: "notif",  idx: number, of: number, value: Value }      // `of` is the command's idx
  | { e: "cancel", idx: number }                                // a cancel signal
  | { e: "output", idx: number, outcome: Outcome }
Cmd =
  | { c: "run",    op: OpName | "sample" | "deadline" }
  | { c: "sleep",  op: OpName | "deadline", ms: number }       // one link
  | { c: "call",   op: OpName }
  | { c: "send",   op: OpName, key: string }
  | { c: "attach", op: OpName, target: string }                // target is the send's key
  | { c: "cancelCall", target: number, by: "executor" | "sdk" } // target is the call or send cmd idx
Value =
  | { ok: unknown }                                            // a sample's ok is its reading
  | { terminal: string }                                       // includes "aborted" and "409"
  | { invocationId: string }                                   // a call's or send's id notification
```

Entries are numbered in journal order. A retryable failure is never an entry.

## Trace events

```
Event =
  | { t: "issue",     fiber, cmdIdx, cmd }              // the executor issued this command (cmd as in Entry)
  | { t: "consume",   entryIdx, entry }                 // the race consumed this journal entry (its content)
  | { t: "sample",    cmdIdx, reading, trueTime }       // a sample applied; trueTime is the environment's
  | { t: "deliver",   fiber, op, value }                // a result reached a fiber
  | { t: "interrupt", fiber, cause: "cancel" | "race" | "timeout" | "closing" }
  | { t: "abort",     op, cause: "interrupt" | "deadline" | "ended" }  // the executor aborted a run's signal
  | { t: "clock",     fiber, L }
  | { t: "draw",      fiber, value }
  | { t: "violation", kind: "blocked" | "refusedAtClosing" | "foreign" | "overflow" | "other" }
  | { t: "freeze" }                                     // a retryable failure is held
  | { t: "warn",      which: 1 | 2, runs: OpName[], tick }
  | { t: "rootExit",  outcome: Outcome }
  | { t: "turn",      cause: "journal" | "local" | "first",
      entryIdx?: number }                 // for "journal": the journal index of its cause
  | { t: "release",   fiber, op, cause: "interrupt" | "race" | "exit" }
  // closure lifecycle, one per run, in trace order (samples included, op "sample:<cmdIdx>"):
  | { t: "wrapper", op, cmdIdx }        // the SDK asked the executor's wrapper for the closure
  | { t: "enter",   op, cmdIdx }        // the wrapper called the closure (an execution)
  | { t: "refuse",  op, cmdIdx }        // the wrapper refused it (terminal abort)
  | { t: "done",    op, cmdIdx, outcome: "ok" | "terminal" | "retryable" | "aborted" }
                                        // the closure itself completed (emitted by the environment)
  | { t: "settle",  op, cmdIdx, outcome: "ok" | "terminal" | "retryable" | "aborted" }
                                        // the executor learned of the completion
  | { t: "propose", op, cmdIdx, outcome: "ok" | "terminal" | "retryable" }
                                        // the executor returned the outcome to the SDK
                                          // a fiber stopped awaiting or owning an operation
```

`fiber` is the fiber id. Ticks are integers; the environment advances them.

## Effects

```
Effect = { op: OpName, attempt: number, entered: boolean | null, signalAbortedAtEntry: boolean,
           settled: "ok" | "terminal" | "retryable" | "aborted" | null }
```

One entry is appended each time the SDK asks for a run's closure. `entered` is false when the
executor's wrapper refused to call the closure, and null when the wrapper was still holding it
(at the entry gate or in the freeze) when the attempt ended. An `entered` entry is one execution of the
external effect.

## Children

```
Child = { key: string | null, viaCmd: number, attempt: number, kind: "call" | "send",
          ran: number, cancelled: boolean, killed: boolean }
```

`ran` counts executions of the child's body across all attempts of the parent.

## The event stream (for monitors)

A monitor reads one invocation as a stream of events, in this order, and never sees the whole
history at once:

```
{ s: "program", program }
for each attempt:
  { s: "attemptStart", n, journalIn }
  each trace event, in order, as { s: "event", event }
  { s: "attemptEnd", end, journalOut, effects }
{ s: "invocationEnd", outcome, children }
```

`model.mjs` exports `streamOf(state)`: the stream of everything that has happened up to `state`, so
the enumerator can feed a monitor the new items after each step. Each monitor is
`{ id, init(): M, step(M, item): M, verdict(M): null | { msg, detail } }` with `M` plain JSON, so
that two monitor states can be compared by their serialization.
