// Pass criteria for R6 (issue #48, step 3, the second warning), fixed
// before the first run. One predicate for the main variant and the
// control.
import { attemptsOf, eventsOf, firstEvent, completedOk } from "./check-lib.mjs";

const probes = [1500, 2500, 3500, 4500];
const onTimeMs = 500;
const stalledMs = 1000;
const graceMs = 1000;
const graceSlackMs = 250;

// Each probe's scheduled completion and its delivery, in ms.
const probeTimes = (events) => {
  const issued = firstEvent(events, "issued")?.ms ?? NaN;
  return probes.map((ms) => ({ ms, due: issued + ms,
    got: firstEvent(events, `tick-p${ms}`, `p${ms}`)?.ms ?? Infinity }));
};

// Probes split into on-time ones followed by stalled ones, with at
// least one of each; otherwise the run does not locate the stall.
const stallBoundary = (times) => {
  const lag = (p) => p.got - p.due;
  const onTime = times.filter((p) => lag(p) < onTimeMs);
  const stalled = times.filter((p) => lag(p) >= stalledMs);
  const ordered = onTime.every((p) => stalled.every((q) => p.due < q.due));
  const usable = onTime.length > 0 && stalled.length > 0 &&
    onTime.length + stalled.length === times.length && ordered;
  return usable ? { lastOnTime: onTime.at(-1), firstStalled: stalled[0] }
    : undefined;
};

const warnings = (events, label) =>
  events.filter((e) => e.label === label && e.detail === "i");

// One grace warning, about a second after the abort.
const graceOk = (events) => {
  const at = firstEvent(events, "abort-point")?.ms ?? NaN;
  const grace = warnings(events, "WARN-grace");
  return grace.length === 1 &&
    Math.abs(grace[0].ms - at - graceMs) <= graceSlackMs;
};

// One inactivity warning, after the last on-time delivery was due and
// no later than the first stalled delivery was due.
const inactivityOk = (events, boundary) => {
  const warn = warnings(events, "WARN-inactivity");
  return boundary !== undefined && warn.length === 1 &&
    warn[0].ms >= boundary.lastOnTime.due &&
    warn[0].ms <= boundary.firstStalled.due;
};

/** R6: the second warning fires where deliveries start to stall. */
export const r6Holds = (run, e) => {
  const events = eventsOf(run, e.id);
  return completedOk(e) && attemptsOf(run, e.id).length === 1 &&
    graceOk(events) &&
    inactivityOk(events, stallBoundary(probeTimes(events)));
};

/** Evidence lines for R6, times in ms after the commands were issued. */
export const r6Evidence = (run, es) => es.flatMap((e) => {
  const events = eventsOf(run, e.id);
  const issued = firstEvent(events, "issued")?.ms ?? 0;
  const rel = (label) => events.filter((x) => x.label === label)
    .map((x) => x.ms - issued).join("|") || "-";
  const probeText = probeTimes(events)
    .map((p) => `p${p.ms}@${p.got - issued}`).join(" ");
  return [`${e.variant} ${e.id} attempts=${attemptsOf(run, e.id).length} ` +
    `status=${e.status?.status}/${e.status?.completion_result}`,
  `  abort=${rel("abort-point")} grace=${rel("WARN-grace")} ` +
    `inactivity=${rel("WARN-inactivity")} i-settle=${rel("i-settle")} ` +
    `probes: ${probeText}`];
});
