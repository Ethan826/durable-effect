import type { ForeignRun } from "./foreign.ts";
import type { LogEntry } from "./host.ts";

// I3's checks on the four runs of foreign.ts, from #37's table: "reaches
// the guard before any handler-observable state changes and before any
// executor action, and the resumed continuation never runs", "a foreign
// interruption leaves σ as it was", and the same trace for two foreign
// values and for any arguments.

/** The host's own notes of foreign calls, outside the runtime's trace. */
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

/**
 * "No executor action": from each foreign resume to the next task sent,
 * the log holds only the host's notes: foreign calls, discarded queues,
 * and `Blocked` when the run has nothing left. Answers the first other
 * entry, described.
 */
const actionAfterResume = (log: ReadonlyArray<LogEntry>) =>
  log.flatMap((entry, at) => {
    if (!isForeignResume(entry)) return [];
    const rest = log.slice(at + 1);
    const next = rest.findIndex((later) => later._tag === "Sent");
    const window = next === -1 ? rest : rest.slice(0, next);
    const action = window.find((later) => later._tag !== "Foreign" &&
      later._tag !== "Discarded" && later._tag !== "Blocked");
    return action === undefined ? [] : [JSON.stringify(action)];
  })[0];

/** Each foreign call reported as foreign, counted against what was sent. */
const unreported = (run: ForeignRun) => {
  const resumes = foreignCount(run, "resume");
  const interrupts = foreignCount(run, "interrupt");
  if (resumes === run.sent.resumes && interrupts === run.sent.interrupts) {
    return undefined;
  }
  return `${run.sent.resumes} resumes and ${run.sent.interrupts} ` +
    `interrupts sent, ${resumes} and ${interrupts} reported foreign`;
};

/** What is wrong with one resuming run, on its own or against baseline. */
const resumeBreach = (baseline: ReadonlyArray<string>) =>
  (run: ForeignRun, at: number) => {
    const name = `resuming run ${at + 1}`;
    if (run.cell !== 0) return `${name}: the continuation wrote ${run.cell}`;
    const counted = unreported(run);
    if (counted !== undefined) return `${name}: ${counted}`;
    const action = actionAfterResume(run.log);
    if (action !== undefined) {
      return `${name}: an executor action after a foreign resume: ${action}`;
    }
    const prefix = beforeResume(run);
    return sameTrace(prefix, baseline.slice(0, prefix.length)) ? undefined
      : `${name}: a foreign interrupt changed the trace`;
  };

/** Foreign interrupts alone: all reported, the whole trace unchanged. */
const interruptsBreach = (
  baseline: ReadonlyArray<string>,
  run: ForeignRun,
) => {
  if (!sameTrace(traceOf(run.log), baseline)) {
    return "interrupt-only run: foreign interrupts changed the trace";
  }
  const counted = unreported(run);
  return counted && `interrupt-only run: ${counted}`;
};

/**
 * I3. The interrupt-only run's whole trace is the baseline's: a foreign
 * interrupt leaves the state as it was. In each resuming run the waiter's
 * continuation never wrote its cell, every foreign call was reported,
 * nothing but host notes follows a foreign resume before the next task,
 * and the trace before the resume is the baseline's. The two resuming
 * runs, with different arguments and values, give the same trace. After
 * a resume the runtime's own bookkeeping may have changed (#37), such as
 * the task counter the discarded yield used, so the baseline is not
 * compared there.
 */
export const i3Breach = (
  runs: ReadonlyArray<ForeignRun>,
): string | undefined => {
  const [baseline, only, first, second] = runs;
  if (!baseline || !only || !first || !second) return "a run is missing";
  const base = traceOf(baseline.log);
  const own = interruptsBreach(base, only) ??
    [first, second].map(resumeBreach(base)).find((breach) => breach);
  return own ?? (sameTrace(traceOf(first.log), traceOf(second.log))
    ? undefined
    : "the two resuming runs' traces differ");
};
