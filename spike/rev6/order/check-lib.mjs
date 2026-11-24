// Reads what a run left behind (out/ and journals/) for check.mjs. Shares
// no code with the handlers: it parses the server's journals, the SDK's
// log and the effects file, and decides nothing itself.
import { readFileSync } from "node:fs";
import { join } from "node:path";

const here = import.meta.dirname;
const lines = (file) =>
  readFileSync(file, "utf8").split("\n").filter((line) => line !== "");

/** Everything one run recorded. */
export const loadRun = () => ({
  manifest: JSON.parse(readFileSync(join(here, "out/manifest.json"))),
  protocol: JSON.parse(readFileSync(join(here, "out/protocol.json"))),
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
    return { ...row, entry: JSON.parse(row.entry_lite_json) };
  });

/** Commands and notifications of a journal in a flat form. */
export const commands = (journal) => journal
  .filter((row) => row.entry.Command !== undefined)
  .map((row) => {
    const [kind, body] = Object.entries(row.entry.Command)[0];
    return { index: row.index, kind, ...body };
  });
export const notifications = (journal) => journal
  .filter((row) => row.entry.Notification !== undefined)
  .map((row) => {
    const { ty, id, result } = row.entry.Notification;
    const kind = typeof ty === "string" ? ty : ty.Completion;
    return { index: row.index, kind, id, result };
  });

/** Run names by completion id, from the journal's Run commands. */
export const runNames = (journal) => new Map(commands(journal)
  .filter((c) => c.kind === "Run")
  .map((c) => [c.completion_id, c.name]));

/** Names of runs in the order their results were journaled. */
export const runResultOrder = (journal) => {
  const names = runNames(journal);
  return notifications(journal)
    .filter((n) => n.kind === "Run")
    .map((n) => names.get(n.id.CompletionId));
};

/** SDK log lines that mention an invocation, in log order. */
export const logOf = (run, id) => run.log.filter((l) => l.includes(id));

export const attemptCount = (run, id) =>
  logOf(run, id).filter((l) => l.startsWith(`ATTEMPT ${id}`)).length;
export const suspensionCount = (run, id) =>
  logOf(run, id).filter((l) => l.endsWith("INFO: Invocation suspended"))
    .length;
/** Attempts that ended neither by suspension nor by completing. */
export const errorAttempts = (run, id) =>
  attemptCount(run, id) - 1 - suspensionCount(run, id);

/** TICK lines of an invocation as { attempt, label, value }. */
export const ticksOf = (run, id) => run.log
  .filter((l) => l.startsWith(`TICK ${id} `))
  .map((l) => {
    const [, , attempt, label, ...rest] = l.split(" ");
    return { attempt: Number(attempt), label, value: rest.join(" ") };
  });

/** The text logged after each WARN line of an invocation. */
export const warnBodies = (run, id) => run.log.flatMap((line, i) => {
  if (!(line.includes(id) && line.includes("WARN:"))) return [];
  const next = run.log.slice(i + 1).findIndex((l) => /^(\[restate\]|[A-Z]+ )/
    .test(l));
  const end = next === -1 ? run.log.length : i + 1 + next;
  return [run.log.slice(i, end).join("\n")];
});

/** Effect lines of an invocation, optionally for one key. */
export const effectsOf = (run, id, key) => run.effects
  .map((l) => l.split(" "))
  .filter(([, inv, k]) => inv === id && (key === undefined || k === key));

/** One line of evidence per invocation for the report. */
export const brief = (run, entry) =>
  `${entry.id} attempts=${attemptCount(run, entry.id)} ` +
  `suspended=${suspensionCount(run, entry.id)} ` +
  `status=${entry.status?.status}/${entry.status?.completion_result}`;

/** A verdict: ok, and the reason it is printed with. */
export const verdict = (ok, reason) => ({ ok, reason });

/** True when every element passes and the list is not empty. */
export const allOf = (items, predicate) =>
  items.length > 0 && items.every(predicate);
