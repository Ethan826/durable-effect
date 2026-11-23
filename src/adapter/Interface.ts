import { Schema } from "effect";

/** A fiber's identity; mirrors Coq `FiberId := nat`. */
export const FiberId = Schema.Natural.pipe(Schema.brand("FiberId"));
/** A fiber's identity; mirrors Coq `FiberId := nat`. */
export type FiberId = typeof FiberId.Type;

/** An await token; mirrors Coq `Token := nat`. */
export const Token = Schema.Natural.pipe(Schema.brand("Token"));
/** An await token; mirrors Coq `Token := nat`. */
export type Token = typeof Token.Type;

/** The name of a task the runtime queued; mirrors Coq `TaskId := nat`. */
export const TaskId = Schema.Natural.pipe(Schema.brand("TaskId"));
/** The name of a task the runtime queued; mirrors Coq `TaskId := nat`. */
export type TaskId = typeof TaskId.Type;

const Millis = Schema.TaggedStruct("Millis", { millis: Schema.Int });
const Forever = Schema.TaggedStruct("Forever", {});

/** A sleep's length; mirrors Coq `Duration`. */
export const Duration = Schema.Union([Millis, Forever]);
/** A sleep's length; mirrors Coq `Duration`. */
export type Duration = typeof Duration.Type;

const Run = Schema.TaggedStruct("Run", {
  kind: Schema.Natural,
  args: Schema.Natural,
});
const Sleep = Schema.TaggedStruct("Sleep", { duration: Duration });

/** A durable operation; mirrors Coq `Op` (`ORun`, `OSleep`). */
export const Op = Schema.Union([Run, Sleep]);
/** A durable operation; mirrors Coq `Op` (`ORun`, `OSleep`). */
export type Op = typeof Op.Type;

const Value = Schema.TaggedStruct("Value", { value: Schema.Natural });
const Failure = Schema.TaggedStruct("Failure", { value: Schema.Natural });

/** What an operation returns to its fiber; mirrors Coq `Outcome`. */
export const Outcome = Schema.Union([Value, Failure]);
/** What an operation returns to its fiber; mirrors Coq `Outcome`. */
export type Outcome = typeof Outcome.Type;

const Success = Schema.TaggedStruct("Success", { value: Schema.Natural });
const ExitFailure = Schema.TaggedStruct("Failure", {
  value: Schema.Natural,
});
const Interrupted = Schema.TaggedStruct("Interrupted", {});
const Defect = Schema.TaggedStruct("Defect", {});

/** The root's exit; mirrors Coq `RootExit` (`ExitSuccess`, ...). */
export const RootExit = Schema.Union([
  Success,
  ExitFailure,
  Interrupted,
  Defect,
]);
/** The root's exit; mirrors Coq `RootExit` (`ExitSuccess`, ...). */
export type RootExit = typeof RootExit.Type;

const StartRoot = Schema.TaggedStruct("StartRoot", {});
const RunQueued = Schema.TaggedStruct("RunQueued", { task: TaskId });
const Deliver = Schema.TaggedStruct("Deliver", {
  fiber: FiberId,
  token: Token,
  outcome: Outcome,
});
const DeliverCancel = Schema.TaggedStruct("DeliverCancel", {
  fiber: FiberId,
  token: Token,
});
const DeliverDefect = Schema.TaggedStruct("DeliverDefect", {
  fiber: FiberId,
  token: Token,
});
const RequestInterrupt = Schema.TaggedStruct("RequestInterrupt", {
  fiber: FiberId,
});

/** A task the executor asks the runtime to run; mirrors Coq `Task`. */
export const Task = Schema.Union([
  StartRoot,
  RunQueued,
  Deliver,
  DeliverCancel,
  DeliverDefect,
  RequestInterrupt,
]);
/** A task the executor asks the runtime to run; mirrors Coq `Task`. */
export type Task = typeof Task.Type;

const Start = Schema.TaggedStruct("Start", {
  fiber: FiberId,
  token: Token,
  op: Op,
});
const Release = Schema.TaggedStruct("Release", {
  fiber: FiberId,
  token: Token,
});
const Queue = Schema.TaggedStruct("Queue", {
  priority: Schema.Natural,
  task: TaskId,
});
const FiberExited = Schema.TaggedStruct("FiberExited", { fiber: FiberId });
const RootExitEvent = Schema.TaggedStruct("RootExit", { exit: RootExit });

/** An event a task reports; mirrors Coq `Event` (`EvStart`, ...). */
export const Event = Schema.Union([
  Start,
  Release,
  Queue,
  FiberExited,
  RootExitEvent,
]);
/** An event a task reports; mirrors Coq `Event` (`EvStart`, ...). */
export type Event = typeof Event.Type;

/** A global that reads time or randomness, or starts a timer. */
export type GlobalSource =
  | "Date.now"
  | "Math.random"
  | "setTimeout"
  | "setImmediate";

/**
 * The executor's side of the interface: what a task may ask of the host.
 * `register` stands for Coq's `Register` question of `Script`. `clock`
 * answers whole milliseconds and `draw` a 32-bit unsigned integer.
 * `noteGlobal` reports that code in a task used one of the logged globals;
 * it is report-only (#37, I2) and changes nothing in the trace.
 */
export interface Host {
  readonly emit: (event: Event) => void;
  readonly clock: (fiber: FiberId) => number;
  readonly draw: (fiber: FiberId) => number;
  readonly register: (fiber: FiberId) => boolean;
  readonly inSlice: () => boolean;
  readonly foreign: (kind: "resume" | "interrupt", fiber: FiberId) => void;
  readonly noteGlobal: (source: GlobalSource) => void;
}

/** The runtime's side of the interface; mirrors Coq `run_task`. */
export interface AdapterRuntime {
  readonly runTask: (task: Task) => void;
}
