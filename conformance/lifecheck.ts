import type { Event, Task, Token } from "../src/adapter/Interface.ts";
import type { LogEntry } from "./host.ts";
import type { LifecycleRun, TaskRecord } from "./lifecycle.ts";
import { coqLog, i4Breach, i6Breach, i8Breach } from "./logprops.ts";

// The checks of I4, I5, I6 and I8 on one lifecycle run (#37's table, the
// "Conformance test" column), and the counts that show what each check
// actually looked at. A finding is a sentence; none is `undefined`.

/** What each check examined in one run, for the scan minimums. */
export interface Scans {
  readonly unmaskedInterrupts: number;
  readonly maskedInterrupts: number;
  readonly lateDeliveries: number;
  readonly cancels: number;
  readonly idleTasks: number;
  readonly successExits: number;
  readonly failureExits: number;
  readonly interruptedExits: number;
  readonly fibers: number;
  readonly internalFibers: number;
  readonly detachedFibers: number;
  readonly closingRegistrations: number;
}

const eventsOf = (entries: ReadonlyArray<LogEntry>): ReadonlyArray<Event> =>
  entries.flatMap((entry) => entry._tag === "Emitted" ? [entry.event] : []);

const entriesOf = (log: ReadonlyArray<LogEntry>, record: TaskRecord) =>
  log.slice(record.from, record.to);

const releases = (entries: ReadonlyArray<LogEntry>) =>
  new Set(eventsOf(entries).flatMap((event) =>
    event._tag === "Release" ? [event.token] : []
  ));

const sentToken = (task: Task) => "token" in task ? [task.token] : [];

/** The tokens `fiber` awaits just before the log's position `at`. */
const awaitedBy = (
  log: ReadonlyArray<LogEntry>,
  at: number,
  fiber: number | undefined,
): ReadonlyArray<Token> => {
  const before = log.slice(0, at);
  const ended = new Set([
    ...before.flatMap((entry) =>
      entry._tag === "Sent" ? sentToken(entry.task) : []
    ),
    ...releases(before),
  ]);
  return eventsOf(before).flatMap((event) =>
    event._tag === "Start" && !ended.has(event.token) &&
      (fiber === undefined || event.fiber === fiber)
      ? [event.token]
      : []
  );
};

const records = (run: LifecycleRun, kind: TaskRecord["kind"]) =>
  run.records.filter((record) => record.kind === kind);

const ranSomething = (record: TaskRecord) =>
  record.loops > 0 || record.to > record.from;

/**
 * Each await open at an interruption request, with Effect's mask on the
 * target as the harness read it before the task (lifecycle.ts), and
 * whether the task reported its release.
 */
const interruptsOf = (run: LifecycleRun) =>
  records(run, "interrupt").flatMap((record) => {
    const target = "fiber" in record.task ? record.task.fiber : -1;
    const released = releases(entriesOf(run.log, record));
    return awaitedBy(run.log, record.from - 1, target).map((token) => ({
      token,
      masked: record.masked,
      released: released.has(token),
      after: record.from,
    }));
  });

type Interrupted = ReturnType<typeof interruptsOf>[number];

/**
 * The branch Effect's mask selects. Unmasked: the release is reported in
 * the interrupt's own task. Masked: no release. A target the registry
 * never saw cannot be judged, which is itself a finding.
 */
const wrongBranch = ({ token, masked, released }: Interrupted) => {
  if (masked === undefined) return `interrupt of an unregistered fiber`;
  if (!masked && !released) {
    return `unmasked await of token ${token} reported no release`;
  }
  return masked && released
    ? `masked await of token ${token} reported a release`
    : undefined;
};

/** A masked await kept through an interruption accepts its delivery. */
const maskedRefused = (run: LifecycleRun) => {
  const masked = interruptsOf(run).filter((one) => one.masked === true);
  return masked.flatMap(({ token, after }) => {
    const delivery = run.records.find((record) => record.from > after &&
      record.kind === "host" && record.task._tag === "Deliver" &&
      record.task.token === token);
    return delivery === undefined || delivery.loops > 0 ? [] :
      [`masked await of token ${token} refused its delivery`];
  })[0];
};

/** A delivered cancellation reports the release of its await. */
const cancelUnreleased = (run: LifecycleRun) =>
  run.records.flatMap((record) => {
    const { task } = record;
    if (task._tag !== "DeliverCancel") return [];
    const open = awaitedBy(run.log, record.from - 1, task.fiber);
    const released = releases(entriesOf(run.log, record));
    return open.includes(task.token) && !released.has(task.token)
      ? [`cancel of token ${task.token} reported no release`]
      : [];
  })[0];

/**
 * I4: Runtime.v's log form (quiet until the await ends, no token twice);
 * the branch Effect's own mask selects at an interruption request; a
 * delivery after a release does nothing; a masked await keeps its
 * delivery; a delivered cancellation releases.
 */
const i4 = (run: LifecycleRun): string | undefined => {
  const late = records(run, "late").find(ranSomething);
  return i4Breach(coqLog(run.log)) ??
    interruptsOf(run).map(wrongBranch).find((found) => found) ??
    (late && `a delivery after the release of ${JSON.stringify(late.task)}` +
      ` ran ${late.loops} loops`) ??
    maskedRefused(run) ?? cancelUnreleased(run);
};

/** I5: a task naming nothing queued runs no loop and logs nothing. */
const i5 = (run: LifecycleRun): string | undefined => {
  const busy = records(run, "idle").find(ranSomething);
  return busy && `an idle task ran ${busy.loops} loops and logged ` +
    `${busy.to - busy.from} entries`;
};

const registrations = (log: ReadonlyArray<LogEntry>) =>
  log.flatMap((entry) =>
    entry._tag === "Answered" && entry.question === "register"
      ? [entry.fiber]
      : []
  );

const count = (log: ReadonlyArray<LogEntry>, tag: Event["_tag"]) =>
  eventsOf(log).filter((event) => event._tag === tag).length;

/** I6: Runtime.v's log form, and exactly one exit once the root exits. */
const i6 = (run: LifecycleRun): string | undefined => {
  const [root] = registrations(run.log);
  const rootGone = eventsOf(run.log).some((event) =>
    event._tag === "FiberExited" && event.fiber === root
  );
  const exits = count(run.log, "RootExit");
  return i6Breach(coqLog(run.log)) ?? (rootGone && exits !== 1
    ? `the root exited and ${exits} root exits were reported`
    : undefined);
};

/** I8: Runtime.v's log form, and the census's fibers, run and exited. */
const i8 = (run: LifecycleRun): string | undefined => {
  const registered = registrations(run.log).length;
  const exited = run.fibers.filter((fiber) => fiber.pollUnsafe()).length;
  const reported = count(run.log, "FiberExited");
  return i8Breach(coqLog(run.log)) ??
    (registered !== run.fibers.length
      ? `${run.fibers.length} fibers ran, ${registered} registered`
      : undefined) ??
    (exited !== reported
      ? `${exited} fibers exited, ${reported} exits reported`
      : undefined);
};

/** Each lifecycle check, by property; I3 has runs of its own. */
export const lifecycleChecks = { I4: i4, I5: i5, I6: i6, I8: i8 } as const;

const exitsTagged = (log: ReadonlyArray<LogEntry>, tag: string) =>
  eventsOf(log).filter((event) =>
    event._tag === "RootExit" && event.exit._tag === tag
  ).length;

/** The root exits by kind: success, typed failure, interruption. */
const exitKinds = (log: ReadonlyArray<LogEntry>) => ({
  successExits: exitsTagged(log, "Success"),
  failureExits: exitsTagged(log, "Failure"),
  interruptedExits: exitsTagged(log, "Interrupted"),
});

/** What one run's checks examined. */
export const scansOf = (run: LifecycleRun): Scans => {
  const interrupts = interruptsOf(run);
  const masked = interrupts.filter((one) => one.masked === true).length;
  return {
    unmaskedInterrupts: interrupts.filter((one) => one.masked === false)
      .length,
    maskedInterrupts: masked,
    lateDeliveries: records(run, "late").length,
    cancels: run.records.filter((record) =>
      record.task._tag === "DeliverCancel"
    ).length,
    idleTasks: records(run, "idle").length,
    ...exitKinds(run.log),
    fibers: run.fibers.length,
    internalFibers: run.kinds.internal,
    detachedFibers: run.kinds.detached,
    closingRegistrations: run.log.filter((entry) =>
      entry._tag === "Answered" && entry.question === "register" &&
      entry.answer === true
    ).length,
  };
};
