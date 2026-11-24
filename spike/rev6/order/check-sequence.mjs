// Checks for F9, F10 and F11 (register on #48, A18, A23, A17).
import {
  entriesOf, journalOf, commands, runResultOrder, ticksOf, effectsOf,
  attemptCount, verdict, allOf
} from "./check-lib.mjs";

// Pinned from the runs of 2026-11-24 against SDK 1.18.4 and server 1.8.1.
const pinned = {
  // F10: the start order of four runs made executable by one race varied
  // between invocations (14 distinct orders in 20 on the first run).
  startOrderVaries: true,
  // F11: every invocation ran on service protocol v7; the deployment
  // advertised 5 to 8.
  protocol: 7,
  deploymentRange: [5, 8]
};

// F9: each attempt's winners, tick by tick, as a list of run names.
const winnersByAttempt = (run, id) => {
  const byAttempt = new Map();
  for (const t of ticksOf(run, id).filter((t) => t.label.startsWith("tick"))) {
    byAttempt.set(t.attempt, [...(byAttempt.get(t.attempt) ?? []),
      JSON.parse(t.value)]);
  }
  return [...byAttempt.values()];
};
const isPrefix = (part, whole) => part.every((name, i) => name === whole[i]);
const followsJournal = (sequences, order) =>
  sequences.some((s) => s.length === order.length) &&
  allOf(sequences, (s) => isPrefix(s, order));

/** F9 tenRuns (A18). */
export const checkF9 = (run) => {
  const entries = [...entriesOf(run, "F9", "replay"),
    ...entriesOf(run, "F9", "live")];
  const cases = entries.map((e) => ({
    e, order: runResultOrder(journalOf(e.journals[0])),
    sequences: winnersByAttempt(run, e.id)
  }));
  const replays = cases.filter((c) => c.sequences.length > 1).length;
  const [first] = cases;
  const swapped = [first.sequences[0][1], first.sequences[0][0],
    ...first.sequences[0].slice(2)];
  return {
    pass: verdict(allOf(cases, (c) => followsJournal(c.sequences, c.order))
      && replays > 0,
    `${cases.length} invocations; every attempt's winners follow the ` +
      `journal's run-result order; ${replays} were replayed`),
    control: verdict(followsJournal([swapped], first.order),
      "same checker on the first invocation's log with ticks 0 and 1 " +
      "swapped"),
    evidence: cases.map((c) => `${c.e.variant} ${c.e.id} journal ` +
      `${c.order.join(",")} attempts ` +
      c.sequences.map((s) => s.join(",")).join(" / "))
  };
};

// F10: start order from the effects file, command order from the journal.
const startOrderOf = (run, id) =>
  effectsOf(run, id).map(([, , key]) => key.replace("start:", ""));
const commandOrderOf = (entry) => commands(journalOf(entry.journals[0]))
  .filter((c) => c.kind === "Run").map((c) => c.name).join(",");
const variesCategory = (orders) => new Set(orders).size > 1;

/** F10 startOrder (A23). */
export const checkF10 = (run) => {
  const entries = entriesOf(run, "F10", "main");
  const orders = entries.map((e) => startOrderOf(run, e.id).join(","));
  const journalOk = allOf(entries, (e) => commandOrderOf(e) ===
    "r1,r2,r3,r4" && attemptCount(run, e.id) === 1);
  const counts = new Map();
  for (const o of orders) counts.set(o, (counts.get(o) ?? 0) + 1);
  const varies = variesCategory(orders);
  return {
    pass: verdict(journalOk && varies === pinned.startOrderVaries,
      `Run commands r1..r4 in every journal: ${journalOk}; ` +
      `${counts.size} distinct start orders in ${orders.length} ` +
      `(pinned: varies=${pinned.startOrderVaries})`),
    control: verdict(variesCategory([orders[0], orders[0]]) ===
      pinned.startOrderVaries,
    "pin checker on a synthetic log with one start order"),
    evidence: [...counts].map(([o, n]) => `${n}x ${o}`)
  };
};

/** F11 protocolVersion (A17). */
export const checkF11 = (run) => {
  const versions = run.manifest.map((e) =>
    e.status?.pinned_service_protocol_version);
  const types = run.log.filter((l) => l.startsWith("REQ /invoke/"))
    .map((l) => l.split(" ")[2]);
  const header = `application/vnd.restate.invocation.v${pinned.protocol}`;
  const [deployment] = run.protocol.deployments;
  const range = [deployment.min_service_protocol_version,
    deployment.max_service_protocol_version];
  const matches = (v) => allOf(versions, (x) => x === v) &&
    allOf(types, (t) => t === `application/vnd.restate.invocation.v${v}`);
  return {
    pass: verdict(matches(pinned.protocol) &&
      range.join() === pinned.deploymentRange.join(),
    `pinned_service_protocol_version ${[...new Set(versions)]} on ` +
      `${versions.length} invocations; ${types.length} invoke requests ` +
      `with ${[...new Set(types)]}; deployment range ${range.join("-")}`),
    control: verdict(matches(pinned.protocol + 1),
      `same check pinned to v${pinned.protocol + 1}`),
    evidence: [`expected ${header}`]
  };
};
