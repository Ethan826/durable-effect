// Reads what a run left behind (out/ and journals/) for check.mjs (O1 to
// O3, issue #48 step 7). Copied from ../rerun/check-lib.mjs. Shares no code with the
// handlers: it parses journals, the SDK log and the effects file.
import { readFileSync } from "node:fs";
import { join } from "node:path";

const here = import.meta.dirname;
const lines = (file) =>
  readFileSync(file, "utf8").split("\n").filter((line) => line !== "");

/** Everything one run recorded. */
export const loadRun = () => ({
  manifest: JSON.parse(readFileSync(join(here, "out/manifest.json"))),
  log: lines(join(here, "out/sdk.log")),
  effects: lines(join(here, "out/effects.log"))
});

/** The manifest entries of one fixture variant. */
export const entriesOf = (run, fixture, variant) =>
  run.manifest.filter((e) => e.fixture === fixture && e.variant === variant);

/** A journal file's rows, with entry_lite_json parsed as `entry`. */
export const journalOf = (file) =>
  lines(join(here, "journals", file)).map((line) => {
    const row = JSON.parse(line);
    return { ...row, entry: JSON.parse(row.entry_lite_json),
      at: Date.parse(row.appended_at) };
  });

const kindOf = (ty) => typeof ty === "string" ? ty : ty.Completion;

/** Run results in a journal for the run named `name`. */
export const runResults = (journal, name) => {
  const ids = journal.filter((r) => r.entry.Command?.Run?.name === name)
    .map((r) => r.entry.Command.Run.completion_id);
  return journal.filter((r) => r.entry.Notification !== undefined &&
    kindOf(r.entry.Notification.ty) === "Run" &&
    ids.includes(r.entry.Notification.id.CompletionId))
    .map((r) => ({ index: r.index, at: r.at, json: r.entry_json,
      result: r.entry.Notification.result }));
};

/** The journal index of the Output command, or Infinity. */
export const outputIndex = (journal) =>
  journal.find((r) => r.entry.Command?.Output !== undefined)?.index ??
    Infinity;

/** ATTEMPT lines of an invocation as { n, ms }. */
export const attemptsOf = (run, id) => run.log
  .filter((l) => l.startsWith(`ATTEMPT ${id} `))
  .map((l) => { const p = l.split(" ");
    return { n: Number(p[3]), ms: Number(p[4]) }; });

export const suspensions = (run, id) => run.log.filter((l) =>
  l.includes(id) && l.endsWith("INFO: Invocation suspended")).length;

/** EV lines of an invocation as { attempt, label, ms, detail }. */
export const eventsOf = (run, id) => run.log
  .filter((l) => l.startsWith(`EV ${id} `))
  .map((l) => { const [, , a, label, ms, ...rest] = l.split(" ");
    return { attempt: Number(a), label, ms: Number(ms),
      detail: rest.join(" ") }; });

/** The first event with a label (and detail, when given). */
export const firstEvent = (events, label, detail) => events.find((e) =>
  e.label === label && (detail === undefined || e.detail === detail));

/** Number of effect lines of an invocation for one key. */
export const effectCount = (run, id, key) => run.effects
  .map((l) => l.split(" ")).filter(([, i, k]) => i === id && k === key)
  .length;

export const completedOk = (e) => e.status?.status === "completed" &&
  e.status?.completion_result === "success";

/** True when every element passes and the list is not empty. */
export const allOf = (items, predicate) =>
  items.length > 0 && items.every(predicate);
/** True when no element passes and the list is not empty. */
export const noneOf = (items, predicate) =>
  items.length > 0 && !items.some(predicate);
