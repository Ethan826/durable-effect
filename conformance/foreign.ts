import { Context, Effect, Random } from "effect";
import type { Durable } from "../src/adapter/Durable.ts";
import { makeAdapter } from "../src/adapter/Runtime.ts";
import type { AnyFiber } from "../src/adapter/State.ts";
import type { Task } from "../src/adapter/Interface.ts";
import { beginRun, fibersRun, openTask } from "./census.ts";
import type { Journal } from "./deliveries.ts";
import type { Program } from "./grammar.ts";
import { scriptedHost } from "./host.ts";
import type { LogEntry, ScriptedHost } from "./host.ts";
import { interpret } from "./interpret.ts";
import type { Variant } from "./mutants.ts";

// I3's runs (#37's table): a program with a foreign waiter added, run
// three times. The baseline sends nothing foreign. The two foreign runs,
// between every pair of tasks, call `interruptUnsafe` on every live
// fiber, and resume the waiter once its callback is waiting, each run
// with its own arguments and value. Neither may change the trace.

/** Which fiber waits for the foreign callback. */
export type Target = "root" | "child" | "detached";

/** Where the foreign waiter sits, and whether a mask encloses it. */
export interface Placement {
  readonly target: Target;
  readonly masked: boolean;
}

/** A foreign run's inputs: the interrupt's arguments, the value. */
interface Inputs {
  readonly args: Parameters<AnyFiber["interruptUnsafe"]>;
  readonly value: number;
}

const foreignInputs: readonly [Inputs, Inputs] = [
  { args: [], value: 1 },
  { args: [42, Context.empty()], value: 2 },
];

/** The waiter's callback, and the cell its continuation writes first. */
interface Point {
  resume: ((effect: Effect.Effect<number>) => void) | undefined;
  cell: number;
}

/** Writes the value to the cell, then draws that many times. */
const continuation = (point: Point) => (value: number) =>
  Effect.andThen(
    Effect.sync(() => {
      point.cell = value;
    }),
    Effect.replicateEffect(Random.next, value),
  );

/** A wait only foreign code ends, masked or not. */
const waiter = (point: Point, masked: boolean) => {
  const wait = Effect.callback<number>((resume) => {
    point.resume = resume;
  }).pipe(Effect.flatMap(continuation(point)));
  return masked ? Effect.uninterruptible(wait) : wait;
};

type Handler = Effect.Effect<unknown, unknown, Durable>;

/** The program with the waiter on the target fiber. */
const placed = (program: Handler, wait: Handler, target: Target) => {
  if (target === "root") return Effect.andThen(Effect.exit(program), wait);
  const fork = target === "child" ? Effect.forkChild : Effect.forkDetach;
  return Effect.andThen(fork(wait), program);
};

/** What a foreign step did, and to which fibers. */
interface Sent {
  interrupts: number;
  resumes: number;
}

/** Interrupts every live fiber, then resumes the waiter once. */
const foreignStep = (point: Point, inputs: Inputs, sent: Sent) => {
  fibersRun().filter((fiber) => fiber.pollUnsafe() === undefined)
    .forEach((fiber) => {
      sent.interrupts += 1;
      fiber.interruptUnsafe(...inputs.args);
    });
  const resume = point.resume;
  if (resume === undefined || sent.resumes > 0) return;
  sent.resumes += 1;
  resume(Effect.succeed(inputs.value));
};

/** One of I3's runs: the log, the cell, and what was sent. */
export interface ForeignRun {
  readonly log: ReadonlyArray<LogEntry>;
  readonly cell: number;
  readonly sent: Sent;
}

/** What one program's I3 runs share. */
interface Setup {
  readonly sampled: readonly [Program, Journal];
  readonly seed: number;
  readonly placement: Placement;
  readonly make: Variant;
}

/** The variant for the program with its waiter, seen by the census. */
const censused = (setup: Setup, point: Point, host: ScriptedHost) => {
  const [program] = setup.sampled;
  const wait = waiter(point, setup.placement.masked);
  const inner = setup.make(
    placed(interpret(program), wait, setup.placement.target), 0, host);
  return {
    runTask: (task: Task) => {
      openTask(() => inner.runTask(task));
    },
  };
};

/** One run, foreign when `inputs` is given, else the baseline. */
const runOnce = async (
  setup: Setup,
  inputs: Inputs | undefined,
): Promise<ForeignRun> => {
  beginRun();
  const point: Point = { resume: undefined, cell: 0 };
  const host = scriptedHost(setup.sampled[1], { seed: setup.seed });
  const adapter = censused(setup, point, host);
  const sent: Sent = { interrupts: 0, resumes: 0 };
  const step = () => inputs && foreignStep(point, inputs, sent);
  await host.runPaced(adapter, async () => step());
  step();
  return { log: host.log, cell: point.cell, sent };
};

/** The baseline and the two foreign runs of one program. */
export const foreignRuns = async (
  sampled: readonly [Program, Journal],
  seed: number,
  placement: Placement,
  make: Variant = makeAdapter,
): Promise<ReadonlyArray<ForeignRun>> => {
  // One after another: the census holds one run's fibers at a time.
  const run = (inputs: Inputs | undefined) =>
    runOnce({ sampled, seed, placement, make }, inputs);
  const [first, second] = foreignInputs;
  return [await run(undefined), await run(first), await run(second)];
};

const hostNote = (entry: LogEntry) => entry._tag === "Foreign" ||
  entry._tag === "Discarded" || entry._tag === "Global";

const isForeignResume = (entry: LogEntry) =>
  entry._tag === "Foreign" && entry.kind === "resume";

/** The trace: the log without the host's notes of foreign calls. */
const traceOf = (log: ReadonlyArray<LogEntry>) =>
  log.filter((entry) => !hostNote(entry)).map((entry) =>
    JSON.stringify(entry)
  );

/** The trace before the first foreign resume: interrupts only. */
const beforeResume = (run: ForeignRun) => {
  const at = run.log.findIndex(isForeignResume);
  return traceOf(at === -1 ? run.log : run.log.slice(0, at));
};

const foreignCount = (run: ForeignRun, kind: "resume" | "interrupt") =>
  run.log.filter((entry) => entry._tag === "Foreign" && entry.kind === kind)
    .length;

const sameTrace = (left: ReadonlyArray<string>, right: ReadonlyArray<string>) =>
  left.length === right.length && left.every((entry, at) =>
    entry === right[at]
  );

/** What is wrong with one foreign run, on its own or against baseline. */
const foreignBreach = (baseline: ReadonlyArray<string>) =>
  (run: ForeignRun, at: number) => {
    const name = `foreign run ${at + 1}`;
    if (run.cell !== 0) return `${name}: the continuation wrote ${run.cell}`;
    const resumes = foreignCount(run, "resume");
    const interrupts = foreignCount(run, "interrupt");
    if (resumes !== run.sent.resumes || interrupts !== run.sent.interrupts) {
      return `${name}: ${run.sent.resumes} resumes and ` +
        `${run.sent.interrupts} interrupts sent, ${resumes} and ` +
        `${interrupts} reported foreign`;
    }
    const prefix = beforeResume(run);
    return sameTrace(prefix, baseline.slice(0, prefix.length)) ? undefined
      : `${name}: a foreign interrupt changed the trace`;
  };

/**
 * I3, #37's test: in each foreign run the waiter's continuation never
 * wrote its cell, and each foreign call was reported as foreign. Before
 * the foreign resume, when only foreign interrupts have been sent, the
 * trace is the baseline's: a foreign interrupt leaves the state as it
 * was. The two foreign runs, with their different arguments and values,
 * give the same trace. After a foreign resume the runtime's own
 * bookkeeping may have changed (#37), such as the task counter that the
 * discarded yield used, so the baseline is not compared there.
 */
export const i3Breach = (
  runs: ReadonlyArray<ForeignRun>,
): string | undefined => {
  const [baseline, first, second] = runs;
  if (baseline === undefined || first === undefined || second === undefined) {
    return "a run is missing";
  }
  const own = [first, second].map(foreignBreach(traceOf(baseline.log)))
    .find((breach) => breach !== undefined);
  return own ?? (sameTrace(traceOf(first.log), traceOf(second.log))
    ? undefined
    : "the two foreign runs' traces differ");
};
