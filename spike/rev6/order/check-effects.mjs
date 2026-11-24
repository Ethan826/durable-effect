// Checks for F17 to F19 (register on #48, A9, A10, A11). Executions are
// counted from the effects file, which the journal does not hold.
import {
  entriesOf, journalOf, notifications, attemptCount, errorAttempts,
  suspensionCount, effectsOf, brief, verdict, allOf
} from "./check-lib.mjs";

// Pinned from the runs of 2026-11-24 against SDK 1.18.4 and server 1.8.1.
const pinned = {
  // F17: the dropped run started once, the attempt suspended while it ran,
  // and no Run result reached the journal.
  f17Executions: 1,
  // F19: the plain Error ended attempt 1; both runs ran again in
  // attempt 2, so the slow run's side effect happened twice.
  f19Attempts: 2, f19SlowExecutions: 2, f19BadExecutions: 2
};

const runResults = (e) => notifications(journalOf(e.journals[0]))
  .filter((n) => n.kind === "Run");
const executions = (run, e, key) => effectsOf(run, e.id, key).length;
const completedOk = (e) => e.status?.status === "completed" &&
  e.status?.completion_result === "success";

// F17: the attempt suspended with the dropped run executing; the run's
// result is not journaled and it did not run again.
const droppedAsPinned = (run, e) => suspensionCount(run, e.id) >= 1 &&
  executions(run, e, "f17run") === pinned.f17Executions &&
  runResults(e).length === 0 && completedOk(e);

/** F17 droppedRunAtSuspension (A9). */
export const checkF17 = (run) => {
  const main = entriesOf(run, "F17", "main");
  const keep = entriesOf(run, "F17", "keep");
  return {
    pass: verdict(allOf(main, (e) => droppedAsPinned(run, e)),
      "suspended while the dropped run executed; executions 1; no Run " +
      "result journaled (pinned)"),
    control: verdict(allOf(keep, (e) => droppedAsPinned(run, e)),
      "same check with the run kept in later races"),
    evidence: [...main, ...keep].map((e) => `${e.variant} ` +
      `${brief(run, e)} executions=${executions(run, e, "f17run")} ` +
      `runResults=${runResults(e).map((n) => n.result)}`)
  };
};

// F18: the run's action never executed.
const neverRan = (run, e) =>
  executions(run, e, "f18run") === 0 && completedOk(e);

/** F18 runExecutesWhen (A10). */
export const checkF18 = (run) => {
  const shapes = ["unraced", "beside", "besideTaken"];
  const cases = shapes.flatMap((s) => ["replay", "live"]
    .flatMap((m) => entriesOf(run, "F18", `${s}-${m}`)));
  const alone = ["replay", "live"]
    .flatMap((m) => entriesOf(run, "F18", `alone-${m}`));
  return {
    pass: verdict(allOf(cases, (e) => neverRan(run, e)),
      "unraced run, run raced beside a queued sleep result, and run " +
      "raced beside an already-taken sleep: executions 0 (live and " +
      "replay)"),
    control: verdict(allOf(alone, (e) => neverRan(run, e)),
      "same check on the run raced alone"),
    evidence: [...cases, ...alone].map((e) => `${e.variant} ` +
      `${brief(run, e)} executions=${executions(run, e, "f18run")}`)
  };
};

// F19: attempts and executions when one of two runs fails retryably.
const asPinned = (run, e) =>
  attemptCount(run, e.id) === pinned.f19Attempts &&
  errorAttempts(run, e.id) === pinned.f19Attempts - 1 &&
  executions(run, e, "f19slow") === pinned.f19SlowExecutions &&
  executions(run, e, "f19bad") === pinned.f19BadExecutions;
const keptAlive = (run, e) => attemptCount(run, e.id) === 1 &&
  executions(run, e, "f19slow") === 1 && completedOk(e);

/** F19 concurrentRetryableFailure (A11). */
export const checkF19 = (run) => {
  const [main] = entriesOf(run, "F19", "main");
  const [terminal] = entriesOf(run, "F19", "terminal");
  return {
    pass: verdict(asPinned(run, main) && keptAlive(run, terminal),
      "plain Error: attempts 2, slow run executed 2 (pinned); " +
      "TerminalError: one attempt, slow run executed 1"),
    control: verdict(asPinned(run, terminal),
      "the pinned plain-Error outcome checked on the TerminalError case"),
    evidence: [main, terminal].map((e) => `${e.variant} ${brief(run, e)} ` +
      `slow=${executions(run, e, "f19slow")} ` +
      `bad=${executions(run, e, "f19bad")}`)
  };
};
