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
// four times. The baseline sends nothing foreign. The other three, between
// every pair of tasks, call `interruptUnsafe` on every live fiber; the
// last two also resume the waiter once its callback is waiting, each with
// its own arguments and value. i3check.ts judges them.

/** Which fiber waits for the foreign callback. */
export type Target = "root" | "child" | "detached";

/** Where the foreign waiter sits, and whether a mask encloses it. */
export interface Placement {
  readonly target: Target;
  readonly masked: boolean;
}

/**
 * A foreign run's inputs: the interrupt's arguments, and the value of
 * the resume, if the run resumes the waiter at all.
 */
interface Inputs {
  readonly args: Parameters<AnyFiber["interruptUnsafe"]>;
  readonly resume: number | undefined;
}

/** Foreign interrupts only; then interrupts and a resume, twice. */
const foreignInputs: readonly [Inputs, Inputs, Inputs] = [
  { args: [42, Context.empty()], resume: undefined },
  { args: [], resume: 1 },
  { args: [42, Context.empty()], resume: 2 },
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
  const value = inputs.resume;
  if (resume === undefined || value === undefined || sent.resumes > 0) return;
  sent.resumes += 1;
  resume(Effect.succeed(value));
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

/**
 * The runs of one program, in order: the baseline; foreign interrupts
 * only; and foreign interrupts with a resume, by each value.
 */
export const foreignRuns = async (
  sampled: readonly [Program, Journal],
  seed: number,
  placement: Placement,
  make: Variant = makeAdapter,
): Promise<ReadonlyArray<ForeignRun>> => {
  // One after another: the census holds one run's fibers at a time.
  const run = (inputs: Inputs | undefined) =>
    runOnce({ sampled, seed, placement, make }, inputs);
  const [only, first, second] = foreignInputs;
  return [
    await run(undefined), await run(only), await run(first),
    await run(second),
  ];
};
