import type {
  Event,
  FiberId,
  Outcome,
  Task,
  Token,
} from "../src/adapter/Interface.ts";

/**
 * A scripted journal. The `n`-th `Run` token, counted from 0 in token
 * order, gets `outcomes[n mod outcomes.length]`, so `Run` tokens take the
 * outcomes in order and start again from the first when they run out. A
 * `Sleep` token of some milliseconds always gets `Value` 0: a real
 * executor completes or cancels a sleep and never fails it. A `Sleep`
 * token of `Forever` never gets a `Value`; only a cancel, an interrupt or
 * the closing defect ends it. `cancelBefore`, when set to `k`, sends a
 * `DeliverCancel` in place of the `k`-th notification (counted from 0), to
 * the fiber awaiting the oldest token at that point, whatever its
 * operation.
 */
export interface Journal {
  readonly outcomes: ReadonlyArray<Outcome>;
  readonly cancelBefore: number | undefined;
}

/** How the host answers one awaited token. */
type Answer =
  | { readonly _tag: "Run"; readonly index: number }
  | { readonly _tag: "Sleep" }
  | { readonly _tag: "Forever" };

/** An awaited token's fiber, and how the host answers it. */
interface Awaited {
  readonly fiber: FiberId;
  readonly answer: Answer;
}

/** What the scripted host keeps to answer awaits from a journal. */
export interface Deliveries {
  readonly awaited: Map<Token, Awaited>;
  delivered: number;
  runs: number;
  cancelled: boolean;
}

/** A start of a durable operation, as the adapter reports it. */
export type Start = Extract<Event, { readonly _tag: "Start" }>;

/** Nothing awaited, nothing delivered, no cancel sent. */
export const freshDeliveries = (): Deliveries => ({
  awaited: new Map(),
  delivered: 0,
  runs: 0,
  cancelled: false,
});

const valueZero: Outcome = { _tag: "Value", value: 0 };

/** Numbers a `Run` among the runs; tells a finite sleep from a forever. */
const answerOf = (state: Deliveries, start: Start): Answer => {
  if (start.op._tag === "Run") return { _tag: "Run", index: state.runs++ };
  return start.op.duration._tag === "Forever"
    ? { _tag: "Forever" }
    : { _tag: "Sleep" };
};

/** Records the await a `Start` opens. */
export const noteStart = (state: Deliveries, start: Start) => {
  state.awaited.set(start.token, {
    fiber: start.fiber,
    answer: answerOf(state, start),
  });
};

/** A run's scripted outcome; `Value` 0 for a finite sleep. */
const outcomeOf = (journal: Journal, answer: Answer): Outcome =>
  answer._tag === "Run"
    ? journal.outcomes[answer.index % journal.outcomes.length] ?? valueZero
    : valueZero;

/** The awaited tokens, lowest first. */
const byToken = (state: Deliveries) =>
  [...state.awaited].sort(([left], [right]) => left - right);

const isDeliverable = ([, awaited]: readonly [Token, Awaited]) =>
  awaited.answer._tag !== "Forever";

/** The scripted cancel, to the oldest await of any operation. */
const cancelOldest = (state: Deliveries): Task | undefined => {
  const oldest = byToken(state)[0];
  if (oldest === undefined) return undefined;
  const [token, { fiber }] = oldest;
  state.awaited.delete(token);
  state.cancelled = true;
  return { _tag: "DeliverCancel", fiber, token };
};

/** The outcome for the oldest await that can get one: not a forever. */
const deliverOldest = (state: Deliveries, journal: Journal) => {
  const oldest = byToken(state).find(isDeliverable);
  if (oldest === undefined) return undefined;
  const [token, { fiber, answer }] = oldest;
  state.awaited.delete(token);
  state.delivered += 1;
  const outcome = outcomeOf(journal, answer);
  return { _tag: "Deliver", fiber, token, outcome } satisfies Task;
};

/**
 * The next notification: the scripted cancel if it is due now, otherwise
 * the oldest deliverable await's outcome; none when nothing can be
 * answered. The await is forgotten first, since the adapter reports no
 * `Release` for an await it resumes.
 */
export const nextNotification = (
  state: Deliveries,
  journal: Journal,
): Task | undefined => {
  const cancelDue = !state.cancelled &&
    state.delivered === journal.cancelBefore;
  return cancelDue ? cancelOldest(state) : deliverOldest(state, journal);
};
