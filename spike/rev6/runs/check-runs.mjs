// Pass criteria for R1 to R3 (issue #48, step 3), fixed before the first
// run. Each predicate is applied to the main variants (must hold on
// every invocation) and to the control variants (must fail on every one).
import {
  entriesOf, journalOf, runResults, outputIndex, attemptsOf, suspensions,
  eventsOf, firstEvent, effectCount, completedOk
} from "./check-lib.mjs";

const journal = (e) => journalOf(e.journals[0]);

// The named run's result: exactly one, a success, before Output.
const journaledBeforeOutput = (e, name) => {
  const j = journal(e);
  const results = runResults(j, name);
  return results.length === 1 && results[0].result === "Success" &&
    results[0].index < outputIndex(j);
};

// R1: every other-work member was first delivered before R settled.
const otherLabels = ["s2", "q", "s3"];
const deliveredBeforeR = (run, e) => {
  const events = eventsOf(run, e.id);
  const settle = firstEvent(events, "r-settle")?.ms ?? Infinity;
  return otherLabels.every((l) =>
    (firstEvent(events, `tick-${l}`, l)?.ms ?? Infinity) < settle);
};

/** R1 neverDropped: one predicate for main and control. */
export const r1Holds = (run, e) => completedOk(e) &&
  journaledBeforeOutput(e, "r") && effectCount(run, e.id, "r") === 1 &&
  deliveredBeforeR(run, e);

/** R2 closingWaits. */
export const r2Holds = (run, e) => completedOk(e) &&
  journaledBeforeOutput(e, "r") && effectCount(run, e.id, "r") === 1;

// R3: A's result appended before B's rejection was even issued.
const aBeforeFailure = (run, e) => {
  const reject = firstEvent(eventsOf(run, e.id), "b-reject")?.ms;
  const results = runResults(journal(e), "a");
  return reject !== undefined && results.length === 1 &&
    results[0].result === "Success" && results[0].at < reject;
};

/** R3 failureHeld. */
export const r3Holds = (run, e) => completedOk(e) &&
  attemptsOf(run, e.id).length === 2 && effectCount(run, e.id, "a") === 1 &&
  aBeforeFailure(run, e);

// R3, settled variant (added after run 1; R3's predicate is unchanged):
// one failed attempt, A executed once, and A's result appended before
// attempt 2 started, that is, by the failed attempt.
const aByFailedAttempt = (run, e) => {
  const second = attemptsOf(run, e.id).find((a) => a.n === 2)?.ms;
  const results = runResults(journal(e), "a");
  return second !== undefined && results.length === 1 &&
    results[0].result === "Success" && results[0].at < second;
};
const failedAttempts = (run, e) =>
  attemptsOf(run, e.id).length - 1 - suspensions(run, e.id);

/** R3s failureHeldUntilSettled. */
export const r3sHolds = (run, e) => completedOk(e) &&
  failedAttempts(run, e) === 1 && effectCount(run, e.id, "a") === 1 &&
  aByFailedAttempt(run, e);

// Per attempt: delivery minus issue for each other-work member.
const latencies = (run, e) => {
  const events = eventsOf(run, e.id);
  const attempts = attemptsOf(run, e.id);
  return attempts.map(({ n, ms }) => {
    const of = (label) => events.find((v) => v.attempt === n &&
      v.label === label);
    const gap = (from, to) => (of(to) && of(from)) ?
      of(to).ms - of(from).ms : "-";
    const first = of("tick-first") ? of("tick-first").ms - ms : "-";
    return `a${n}: first=${first} ` + otherLabels.map((l) =>
      `${l}=${gap(`issue-${l}`, `tick-${l}`)}`).join(" ");
  }).join(" | ");
};

const brief = (run, e) => `${e.variant} ${e.id} ` +
  `attempts=${attemptsOf(run, e.id).length} ` +
  `suspended=${suspensions(run, e.id)} ` +
  `status=${e.status?.status}/${e.status?.completion_result}`;

const resultsLine = (e, name) => JSON.stringify(runResults(journal(e), name)
  .map((r) => ({ index: r.index, result: r.result })));

/** Evidence lines for R1. */
export const r1Evidence = (run, es) => es.flatMap((e) => {
  const events = eventsOf(run, e.id);
  const settle = firstEvent(events, "r-settle")?.ms;
  const ticks = events.filter((v) => v.label.startsWith("tick-"))
    .map((v) => `${v.attempt}:${v.label.slice(5)}=${v.detail}` +
      `@${v.ms - (settle ?? 0)}`).join(" ");
  return [`${brief(run, e)} rEffects=${effectCount(run, e.id, "r")} ` +
    `rResults=${resultsLine(e, "r")} output=${outputIndex(journal(e))}`,
  `  ticks (ms relative to r-settle): ${ticks}`,
  `  latency ms (issue to delivery): ${latencies(run, e)}`];
});

/** Evidence lines for R2. */
export const r2Evidence = (run, es) => es.map((e) => `${brief(run, e)} ` +
  `rEffects=${effectCount(run, e.id, "r")} ` +
  `rResults=${resultsLine(e, "r")} output=${outputIndex(journal(e))}`);

// R3: the entries appended before attempt 2 started.
const failedAttemptEntries = (run, e) => {
  const second = attemptsOf(run, e.id).find((a) => a.n === 2)?.ms;
  return journal(e).filter((r) => second !== undefined && r.at < second)
    .map((r) => `${r.index}:${r.entry_type}` +
      `${r.name ? `(${r.name})` : ""}` +
      `${r.entry.Notification ? `=${r.entry.Notification.result}` : ""}`)
    .join(", ");
};

/** Evidence lines for R3. */
export const r3Evidence = (run, es) => es.flatMap((e) => [
  `${brief(run, e)} aEffects=${effectCount(run, e.id, "a")} ` +
  `bEffects=${effectCount(run, e.id, "b")} ` +
  `aResults=${resultsLine(e, "a")} bResults=${resultsLine(e, "b")} ` +
  `aJournaledBeforeReject=${aBeforeFailure(run, e)} ` +
  `aJournaledByFailedAttempt=${aByFailedAttempt(run, e)} ` +
  `failedAttempts=${failedAttempts(run, e)}`,
  `  appended before attempt 2: ${failedAttemptEntries(run, e)}`]);

export { entriesOf };
