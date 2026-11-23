import { Context, Data, Effect, Match, Option } from "effect";
import type { FiberId, Host, Op, Outcome, Task, Token } from "./Interface.ts";
import { freshToken } from "./State.ts";
import type { AdapterState, AnyFiber } from "./State.ts";

/**
 * The adapter's durable operations, provided to the handler by
 * `makeAdapter`. `await` starts `op` and waits for the executor's answer:
 * a `Value` succeeds with its natural, a `Failure` fails with it.
 */
export class Durable extends Context.Service<Durable, {
  readonly await: (op: Op) => Effect.Effect<number, number>;
}>()("durable-effect/adapter/Durable") {}

/** Starts a durable operation and awaits its outcome; see {@link Durable}. */
export const durable = (op: Op): Effect.Effect<number, number, Durable> =>
  Effect.flatMap(Effect.service(Durable), (service) => service.await(op));

/**
 * The defect of an await on a fiber the adapter never registered, which
 * happens only under `PreventSchedulerYield`: it has no id to report.
 */
export class UnregisteredFiber extends Data.TaggedError(
  "UnregisteredFiber",
) {}

/** The defect `DeliverDefect` resumes with: the executor refused the op. */
export class RefusedOperation extends Data.TaggedError("RefusedOperation") {}

/** Forgets the await and reports that its fiber unwound out of it. */
const releaseOf = (
  state: AdapterState,
  host: Host,
  fiber: FiberId,
  token: Token,
) => Effect.sync(() => {
  state.awaits.delete(token);
  host.emit({ _tag: "Release", fiber, token });
});

/**
 * One await on a registered fiber. Effect runs the returned cleanup only
 * when the fiber unwinds with an interrupt, first among its finalizers, and
 * not while a mask defers the interrupt (effect 4.1.5 internal/effect.ts
 * :1208-1276). So `Release` means the fiber really left the await.
 */
const awaitOn = (
  state: AdapterState,
  host: Host,
  op: Op,
  fiber: FiberId,
) => Effect.callback<number, number>((resume) => {
  const token = freshToken(state);
  state.awaits.set(token, { fiber, resume });
  host.emit({ _tag: "Start", fiber, token, op });
  return releaseOf(state, host, fiber, token);
});

/** The await for `op` on the given fiber, if the adapter registered it. */
const awaitOnFiber = (state: AdapterState, host: Host, op: Op) =>
  (fiber: AnyFiber) =>
    Option.match(Option.fromUndefinedOr(state.fibers.get(fiber)), {
      onNone: () => Effect.die(new UnregisteredFiber()),
      onSome: (known) => awaitOn(state, host, op, known.id),
    });

/** The `Durable` service for one adapter's state and host. */
export const makeDurable = (state: AdapterState, host: Host) =>
  Durable.of({
    await: (op) => Effect.withFiber(awaitOnFiber(state, host, op)),
  });

/** The three tasks that answer an await. */
export type Delivery = Extract<
  Task,
  { readonly _tag: "Deliver" | "DeliverCancel" | "DeliverDefect" }
>;

const fromOutcome = (outcome: Outcome) =>
  Match.value(outcome).pipe(Match.tagsExhaustive({
    Value: (answer) => Effect.succeed(answer.value),
    Failure: (answer) => Effect.fail(answer.value),
  }));

/** What the awaiting fiber resumes with for each delivery. */
const resumptionOf = (delivery: Delivery): Effect.Effect<number, number> =>
  Match.value(delivery).pipe(Match.tagsExhaustive({
    Deliver: (task) => fromOutcome(task.outcome),
    DeliverCancel: () => Effect.interrupt,
    DeliverDefect: () => Effect.die(new RefusedOperation()),
  }));

/**
 * Resumes the fiber awaiting the delivery's token, and forgets the await
 * first, so a token is answered at most once. A delivery for a token that
 * is not awaited, or not by that fiber, does nothing.
 */
export const deliver = (state: AdapterState, delivery: Delivery) => {
  const pending = state.awaits.get(delivery.token);
  if (pending === undefined || pending.fiber !== delivery.fiber) return;
  state.awaits.delete(delivery.token);
  pending.resume(resumptionOf(delivery));
};
