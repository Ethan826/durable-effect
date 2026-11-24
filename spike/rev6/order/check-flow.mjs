// Checks for F5 to F8 (register on #48, A19, A20, A21, A22).
import {
  entriesOf, journalOf, commands, notifications, attemptCount,
  errorAttempts, ticksOf, effectsOf, brief, verdict, allOf
} from "./check-lib.mjs";

// Pinned from the runs of 2026-11-24 against SDK 1.18.4 and server 1.8.1.
const pinned = {
  // F6 case 4: the dropped run's retryable failure ended attempt 1; the
  // run did not execute again and left no result in the journal.
  retryErrorAttempts: 1, retryExecutions: 1,
  // F7: the run executing when the root returned ran to its end.
  f7RunStarts: 1, f7RunEnds: 1
};

const completedOk = (e) => e.status?.status === "completed" &&
  e.status?.completion_result === "success";
const members = ["call1", "call2", "run1", "run2", "sleep1", "sleep2",
  "awk", "resolver"];

// F5: no attempt beyond those suspensions explain, every member won.
const noExtraAttempts = (run, e) =>
  errorAttempts(run, e.id) === 0 && completedOk(e);
const allMembersWon = (run, e) => {
  const last = attemptCount(run, e.id);
  const won = ticksOf(run, e.id).filter((t) => t.attempt === last)
    .map((t) => JSON.parse(t.value));
  return members.every((m) => won.includes(m));
};

/** F5 manyInFlight (A19). */
export const checkF5 = (run) => {
  const live = entriesOf(run, "F5", "live");
  const replay = entriesOf(run, "F5", "replay");
  const [control] = entriesOf(run, "F5", "subscribedLonger");
  const ok = allOf(live, (e) => attemptCount(run, e.id) === 1) &&
    allOf([...live, ...replay], (e) => noExtraAttempts(run, e) &&
      allMembersWon(run, e));
  return {
    pass: verdict(ok, "8 members (2 calls, 2 runs, 2 sleeps, awakeable, " +
      "resolver call) over 8 ticks; live in one attempt, replay with " +
      "no attempt beyond its suspensions"),
    control: verdict(noExtraAttempts(run, control),
      "same check on #31's subscribedLonger pattern"),
    evidence: [...live, ...replay, control].map((e) => brief(run, e))
  };
};

// F6: the dropped operation's failure is journaled; no failed attempt.
const failureKinds = { call: "Call", run: "Run", awk: "Signal" };
const failureJournaled = (e, kind) =>
  notifications(journalOf(e.journals[0]))
    .some((n) => n.kind === failureKinds[kind] && n.result === "Failure");
const leftAlone = (run, e) => errorAttempts(run, e.id) === 0 &&
  completedOk(e);
const retryAsPinned = (run, e) =>
  errorAttempts(run, e.id) === pinned.retryErrorAttempts &&
  effectsOf(run, e.id, "f6run:retryable").length ===
    pinned.retryExecutions &&
  !notifications(journalOf(e.journals[0])).some((n) => n.kind === "Run") &&
  completedOk(e);

/** F6 droppedFailures (A20). */
export const checkF6 = (run) => {
  const cases = ["call", "run", "awk"].flatMap((kind) =>
    ["live", "replay"].flatMap((mode) =>
      entriesOf(run, "F6", `${kind}-${mode}`).map((e) => ({ kind, e }))));
  const retry = ["live", "replay"]
    .flatMap((mode) => entriesOf(run, "F6", `retry-${mode}`));
  return {
    pass: verdict(allOf(cases, ({ kind, e }) => failureJournaled(e, kind)
      && leftAlone(run, e)) && allOf(retry, (e) => retryAsPinned(run, e)),
    "call, run and awakeable failures journaled with no failed attempt " +
      "(live and replay); retryable run as pinned: 1 failed attempt, " +
      "1 execution, no Run result"),
    control: verdict(allOf(retry, (e) => leftAlone(run, e)),
      "the no-failed-attempt check on the retryable dropped run"),
    evidence: [...cases.map(({ e }) => e), ...retry].map((e) =>
      `${e.variant} ${brief(run, e)} executions=` +
      effectsOf(run, e.id).length)
  };
};

// F7: one attempt; nothing reaches the journal after the Output.
const kindsAfterOutput = (journal) => {
  const output = commands(journal).find((c) => c.kind === "Output");
  return journal.filter((r) => r.index > output.index)
    .map((r) => r.entry_type);
};

/** F7 returnsMidRace (A21). */
export const checkF7 = (run) => {
  const [main] = entriesOf(run, "F7", "main");
  const [control] = entriesOf(run, "F7", "returnsWithPending");
  const [, late] = main.journals.map(journalOf);
  const resultKinds = notifications(late).map((n) => n.kind);
  const effects = (key) => effectsOf(run, main.id, key).length;
  const child = main.children[0]?.status;
  const ok = attemptCount(run, main.id) === 1 && completedOk(main) &&
    kindsAfterOutput(late).length === 0 &&
    !resultKinds.includes("Run") && !resultKinds.includes("Call") &&
    effects("f7run:start") === pinned.f7RunStarts &&
    effects("f7run:end") === pinned.f7RunEnds && child === "completed";
  return {
    pass: verdict(ok, "one attempt; 3 s after completion the journal " +
      "holds no Run or Call result and nothing after Output; the run " +
      "ran to its end (pinned); the child call completed"),
    control: verdict(attemptCount(run, control.id) === 1,
      "the one-attempt check on #31's returnsWithPending"),
    evidence: [brief(run, main), `late journal notifications: ` +
      resultKinds.join(","), `child ${JSON.stringify(main.children)}`,
    brief(run, control)]
  };
};

// F8: the child starts at least one turn (2 s) after the call is issued.
const stamp = (run, prefix, id) => Number(run.log
  .find((l) => l.startsWith(`${prefix} ${id} `))?.split(" ")[2]);
const delays = (run, e) => ({
  childAfterIssue: stamp(run, "CHILDSTART", e.id) - stamp(run, "ISSUE", e.id),
  childAfterTurn: stamp(run, "CHILDSTART", e.id) - stamp(run, "TURNEND", e.id)
});
const startsAfterTurn = (run, e) => delays(run, e).childAfterIssue >= 2000;

/** F8 commandsAtAwait (A22). */
export const checkF8 = (run) => {
  const main = entriesOf(run, "F8", "main");
  const atOnce = entriesOf(run, "F8", "atOnce");
  return {
    pass: verdict(allOf(main, (e) => startsAfterTurn(run, e) &&
      delays(run, e).childAfterTurn >= 0),
    "child started at or after the end of the 2 s turn"),
    control: verdict(allOf(atOnce, (e) => startsAfterTurn(run, e)),
      "the same check when the call is raced at once"),
    evidence: [...main, ...atOnce].map((e) =>
      `${e.variant} ${e.id} ${JSON.stringify(delays(run, e))}`)
  };
};

