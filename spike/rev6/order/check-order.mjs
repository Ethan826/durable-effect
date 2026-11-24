// Checks for F1 to F4 (register on #48, A1, A2, A12, A14). Each check
// returns its verdict on the fixture and on the fixture's control; the
// control's verdict must be a failure.
import {
  entriesOf, journalOf, notifications, runNames, logOf, attemptCount,
  errorAttempts, ticksOf, warnBodies, brief, verdict, allOf
} from "./check-lib.mjs";

const final = (entry) => journalOf(entry.journals[0]);
const raceTicks = (run, id) =>
  ticksOf(run, id).filter((t) => t.label === "race");
const replayed = (ticks) => ticks.some((t) => t.attempt > 1);

// Journal index of each run's result, by run name.
const runResultIndex = (journal) => {
  const names = runNames(journal);
  return new Map(notifications(journal).filter((n) => n.kind === "Run")
    .map((n) => [names.get(n.id.CompletionId), n.index]));
};

// F1: the winner is the run whose result has the lower journal index.
const lowerIndexWins = (run, entry) => {
  const at = runResultIndex(final(entry));
  const expected = at.get("a") < at.get("b") ? "a" : "b";
  const ticks = raceTicks(run, entry.id);
  return replayed(ticks) &&
    allOf(ticks, (t) => t.value === JSON.stringify(expected));
};
const adjacency = (entry) => {
  const at = runResultIndex(final(entry));
  return Math.abs(at.get("a") - at.get("b")) === 1;
};

/** F1 adjacentReplay (A1). */
export const checkF1 = (run) => {
  const main = entriesOf(run, "F1", "main");
  const changed = entriesOf(run, "F1", "changed");
  const winners = main.map((e) => raceTicks(run, e.id)
    .map((t) => `${t.attempt}:${t.value}`).join(" "));
  return {
    pass: verdict(allOf(main, (e) => lowerIndexWins(run, e)),
      `${main.length} invocations; lower journal index won in every ` +
      `attempt; adjacent results in ` +
      `${main.filter(adjacency).length}/${main.length}`),
    control: verdict(changed.some((e) => lowerIndexWins(run, e)),
      "race changed on replay to the live loser; checker verdicts: " +
      changed.map((e) => lowerIndexWins(run, e) ? "pass" : "fail")
        .join(",")),
    evidence: winners.map((w, i) => `${main[i].id} ${w}`)
  };
};

// F2: sleep b (300 ms) is journaled before a (600 ms), both before the
// slow run's result, so both are ready when the race starts.
const sleepIndex = (journal) => {
  const sleeps = journal.filter((r) => r.entry_type === "Command: Sleep");
  const byId = new Map(notifications(journal).filter((n) => n.kind ===
    "Sleep").map((n) => [n.id.CompletionId, n.index]));
  const completion = (row) => row.entry.Command.Sleep.completion_id;
  return { a: byId.get(completion(sleeps[0])),
    b: byId.get(completion(sleeps[1])) };
};
const bothReady = (entry) => {
  const journal = final(entry);
  const { a, b } = sleepIndex(journal);
  return b < a && a < runResultIndex(journal).get("slow");
};
// A replay variant must have raced on replay, a live one in attempt 1.
const winsEveryAttempt = (run, entry, name) => {
  const ticks = raceTicks(run, entry.id);
  const covered = entry.variant.endsWith("-live")
    ? ticks.some((t) => t.attempt === 1) : replayed(ticks);
  return covered && allOf(ticks, (t) => t.value === JSON.stringify(name));
};
const journalEarliest = (entry) => {
  const { a, b } = sleepIndex(final(entry));
  return a < b ? "a" : "b";
};

/** F2 subsetThenRace (A2). */
export const checkF2 = (run) => {
  const main = [...entriesOf(run, "F2", "main"),
    ...entriesOf(run, "F2", "main-live")];
  const reversed = [...entriesOf(run, "F2", "reversed"),
    ...entriesOf(run, "F2", "reversed-live")];
  const ready = [...main, ...reversed].every(bothReady);
  const order = allOf(main, (e) => winsEveryAttempt(run, e, "a")) &&
    allOf(reversed, (e) => winsEveryAttempt(run, e, "b"));
  return {
    pass: verdict(ready && order,
      `both sleeps ready before the race: ${ready}; ` +
      `[a,b] gives a and [b,a] gives b in every attempt: ${order}`),
    control: verdict(allOf(main, (e) =>
      winsEveryAttempt(run, e, journalEarliest(e))),
    "journal-earliest-wins checker on the [a,b] invocations (live and " +
      "replay)"),
    evidence: [...main, ...reversed].map((e) => `${e.variant} ${e.id} ` +
      raceTicks(run, e.id).map((t) => `${t.attempt}:${t.value}`).join(" "))
  };
};

// F3: an attempt fails with "awaitNext already pending".
const awaitNextFailures = (run, id) => warnBodies(run, id)
  .filter((body) => body.includes("awaitNext already pending")).length;
const failsWithAwaitNext = (run, entry) =>
  errorAttempts(run, entry.id) >= 1 && awaitNextFailures(run, entry.id) >= 1;

/** F3 replacedRace (A12), a must-fail gate. */
export const checkF3 = (run) => {
  const [main] = entriesOf(run, "F3", "main");
  const [dropped] = entriesOf(run, "F3", "dropped");
  const last = ticksOf(run, main.id).at(-1);
  return {
    pass: verdict(failsWithAwaitNext(run, main),
      `${errorAttempts(run, main.id)} attempts failed, ` +
      `${awaitNextFailures(run, main.id)} with awaitNext already pending`),
    control: verdict(failsWithAwaitNext(run, dropped),
      "the same gate on the dropped (unsubscribed) first race"),
    evidence: [brief(run, main), `last tick ${JSON.stringify(last)}`,
      brief(run, dropped)]
  };
};

// F4: between TURN start n and TURN end n, no suspension and no attempt.
const quietTurn = (lines, id, n) => {
  const start = lines.indexOf(`TURN start ${id} ${n}`);
  const end = lines.indexOf(`TURN end ${id} ${n}`);
  const inside = lines.slice(start + 1, end);
  return start !== -1 && end > start && !inside.some((l) =>
    l.endsWith("Invocation suspended") || l.startsWith(`ATTEMPT ${id}`));
};
const noSuspensionMidTurn = (run, entry) => {
  const lines = logOf(run, entry.id);
  const attempts = attemptCount(run, entry.id);
  const numbers = Array.from({ length: attempts }, (_, i) => i + 1);
  return attempts > 1 && numbers.every((n) => quietTurn(lines, entry.id, n));
};

/** F4 turnWithoutRace (A14). */
export const checkF4 = (run) => {
  const main = entriesOf(run, "F4", "main");
  const subscribed = entriesOf(run, "F4", "subscribed");
  return {
    pass: verdict(allOf(main, (e) => noSuspensionMidTurn(run, e)),
      "no suspension or new attempt inside any 2 s turn; " +
      "the invocation still suspended later (attempts > 1)"),
    control: verdict(subscribed.some((e) => noSuspensionMidTurn(run, e)),
      "same check with the pending sleep subscribed by then()"),
    evidence: [...main, ...subscribed].map((e) => `${e.variant} ` +
      brief(run, e) + " log: " + logOf(run, e.id)
        .filter((l) => /TURN|suspended|^ATTEMPT/.test(l))
        .map((l) => l.replace(e.id, "").replace(/^\[restate\].*\] /, ""))
        .join(" | "))
  };
};
