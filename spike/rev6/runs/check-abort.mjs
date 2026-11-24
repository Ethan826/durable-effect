// Pass criteria for R4 (issue #48, step 3, abort signal), fixed before
// the first run.
import {
  journalOf, runResults, attemptsOf, eventsOf, firstEvent, slowLines,
  completedOk
} from "./check-lib.mjs";

const promptMs = 1000;

// W settled within a second of the abort point (the abort, when made).
const wPrompt = (events) => {
  const point = firstEvent(events, "abort-point")?.ms;
  const settle = firstEvent(events, "w-settle")?.ms;
  return point !== undefined && settle !== undefined &&
    settle - point < promptMs;
};

// W's outcome journaled as a terminal failure carrying the abort.
const wTerminal = (journal) => {
  const results = runResults(journal, "w");
  return results.length === 1 && results[0].result === "Failure" &&
    results[0].json.includes("aborted");
};

// I settled with success, only after the slow server answered it.
const iAfterAnswer = (run, events, journal) => {
  const start = firstEvent(events, "i-start")?.ms;
  const settle = firstEvent(events, "i-settle", "ok")?.ms;
  const sent = slowLines(run).some((s) => s.what === "SENT" &&
    s.label === "i" && s.ms >= start && s.ms <= settle);
  const results = runResults(journal, "i");
  return sent && results.length === 1 && results[0].result === "Success";
};

const warned = (events, label) =>
  events.some((e) => e.label === `WARN-unsettled-${label}`);

/** R4 abortLoser: one predicate for main and both controls. */
export const r4Holds = (run, e) => {
  const events = eventsOf(run, e.id);
  const journal = journalOf(e.journals[0]);
  return completedOk(e) && attemptsOf(run, e.id).length === 1 &&
    wPrompt(events) && wTerminal(journal) &&
    iAfterAnswer(run, events, journal) &&
    warned(events, "i") && !warned(events, "w");
};

const since = (events, label, from) => {
  const at = firstEvent(events, label)?.ms;
  return at === undefined ? "-" : at - from;
};

/** Evidence lines for R4. */
export const r4Evidence = (run, es) => es.flatMap((e) => {
  const events = eventsOf(run, e.id);
  const point = firstEvent(events, "abort-point")?.ms ?? 0;
  const journal = journalOf(e.journals[0]);
  const results = (n) => JSON.stringify(runResults(journal, n)
    .map((r) => ({ index: r.index, result: r.result })));
  return [`${e.variant} ${e.id} attempts=${attemptsOf(run, e.id).length} ` +
    `status=${e.status?.status}/${e.status?.completion_result} ` +
    `wResults=${results("w")} iResults=${results("i")}`,
  `  ms after abort-point: w-settle=${since(events, "w-settle", point)} ` +
    `(${firstEvent(events, "w-settle")?.detail}) ` +
    `i-settle=${since(events, "i-settle", point)} ` +
    `(${firstEvent(events, "i-settle")?.detail}) ` +
    `warn-i=${since(events, "WARN-unsettled-i", point)} ` +
    `warn-w=${since(events, "WARN-unsettled-w", point)}`];
});
