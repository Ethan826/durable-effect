// Talks to the Restate server for drive.mjs: sends invocations, waits for
// them, reads sys_invocation and sys_journal, writes journals as JSON
// lines under journals/.
import { writeFileSync } from "node:fs";
import { join } from "node:path";

const admin = "http://127.0.0.1:19900";
const ingress = "http://127.0.0.1:19901";
const journalDir = join(import.meta.dirname, "journals");
const json = { "content-type": "application/json", accept: "application/json" };

/** Runs one SQL query against the admin API and returns its rows. */
export const query = async (sql) => {
  const response = await fetch(`${admin}/query`, {
    method: "POST", headers: json, body: JSON.stringify({ query: sql })
  });
  return (await response.json()).rows;
};

/** Sends an invocation without waiting; returns its invocation id. */
export const send = async (service, handler, body = null) => {
  const response = await fetch(`${ingress}/${service}/${handler}/send`, {
    method: "POST", headers: json, body: JSON.stringify(body)
  });
  return (await response.json()).invocationId;
};

const statusColumns = [
  "id", "target", "status", "retry_count", "completion_result",
  "completion_failure", "last_failure", "pinned_service_protocol_version",
  "pinned_deployment_id", "invoked_by_id"
].join(", ");

/** The sys_invocation row of one invocation. */
export const statusOf = async (id) =>
  (await query(
    `SELECT ${statusColumns} FROM sys_invocation WHERE id = '${id}'`))[0];

/** The sys_invocation rows of the calls an invocation made. */
export const childrenOf = (id) =>
  query(`SELECT ${statusColumns} FROM sys_invocation
    WHERE invoked_by_id = '${id}'`);

export const sleep = (ms) =>
  new Promise((resolve) => setTimeout(resolve, ms));

/** Polls until the invocation completes or the timeout passes. */
export const waitDone = async (id, timeoutMs) => {
  const deadline = Date.now() + timeoutMs;
  let row = await statusOf(id);
  while (row?.status !== "completed" && Date.now() < deadline) {
    await sleep(200);
    row = await statusOf(id);
  }
  return row;
};

/** Kills an invocation through the admin API; returns the HTTP status. */
export const kill = async (id) =>
  (await fetch(`${admin}/invocations/${id}/kill`, { method: "PATCH" }))
    .status;

const journalColumns = [
  "index", "entry_type", "name", "completed", "invoked_id",
  "invoked_target", "sleep_wakeup_at", "version", "appended_at",
  "entry_lite_json", "entry_json"
].join(", ");

/** Reads an invocation's journal and writes it to journals/<file>. */
export const dumpJournal = async (id, file) => {
  const rows = await query(`SELECT ${journalColumns} FROM sys_journal
    WHERE id = '${id}' ORDER BY index`);
  const lines = rows.map((row) => JSON.stringify({ id, ...row }));
  writeFileSync(join(journalDir, file), lines.join("\n") + "\n");
  return file;
};
