// Pass criteria for R5 (issue #48, step 3, re-abort on replay), fixed
// before the first run. One predicate for the main variant and the
// control.
import {
  journalOf, runResults, attemptsOf, eventsOf, effectCount, completedOk
} from "./check-lib.mjs";

// r's only journaled result is a terminal failure carrying the abort.
const terminalAbort = (journal) => {
  const results = runResults(journal, "r");
  return results.length === 1 && results[0].result === "Failure" &&
    results[0].json.includes("aborted");
};

// The last attempt's execution of r started with its signal aborted.
const lastStartAborted = (events, attempts) => {
  const starts = events.filter((e) => e.label === "r-start" &&
    e.attempt === attempts);
  return starts.length === 1 && starts[0].detail === "aborted";
};

/** R5: attempt 1 lost r's result, and a later attempt ended the loop
 * by aborting r before its work started. */
export const r5Holds = (run, e) => {
  const attempts = attemptsOf(run, e.id).length;
  return completedOk(e) && attempts >= 2 &&
    terminalAbort(journalOf(e.journals[0])) &&
    effectCount(run, e.id, "r") === 1 &&
    lastStartAborted(eventsOf(run, e.id), attempts);
};

// One attempt's r and abort events as text, times from attempt start.
const attemptLine = (run, id) => ({ n, ms }) => {
  const events = eventsOf(run, id).filter((e) => e.attempt === n);
  const pick = (label) => events.filter((e) => e.label === label)
    .map((e) => `${e.ms - ms}${e.detail ? `:${e.detail}` : ""}`).join("|");
  return `  attempt ${n}: r-start=${pick("r-start") || "-"} ` +
    `tick-first=${pick("tick-first") || "-"} ` +
    `abort-point=${pick("abort-point") || "-"} ` +
    `r-settle=${pick("r-settle") || "-"}`;
};

/** Evidence lines for R5. */
export const r5Evidence = (run, es) => es.flatMap((e) => {
  const results = runResults(journalOf(e.journals[0]), "r")
    .map((r) => ({ index: r.index, result: r.result }));
  return [`${e.variant} ${e.id} attempts=${attemptsOf(run, e.id).length} ` +
    `status=${e.status?.status}/${e.status?.completion_result} ` +
    `rEffects=${effectCount(run, e.id, "r")} ` +
    `rResults=${JSON.stringify(results)}`,
  ...attemptsOf(run, e.id).map(attemptLine(run, e.id))];
});
