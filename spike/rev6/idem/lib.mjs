// Helpers for the rev6-idem fixtures, adapted from ../cancel/lib.mjs: the server and SDK processes,
// admin and ingress calls, sys_journal queries, journal dumps, the SDK log, the counter file and
// the RESULT and CONTROL verdict lines.
// Environment (set by run.sh): SERVER_BIN, SDK_DIR, STATE_DIR, OUT_DIR, COUNTER_FILE.
import { spawn } from "node:child_process";
import { mkdirSync, openSync, readFileSync, writeFileSync } from "node:fs";
import { setTimeout as sleep } from "node:timers/promises";

const ADMIN = "http://127.0.0.1:19920";
const INGRESS = "http://127.0.0.1:19921";
const SDK_PORT = 19922;
const { SERVER_BIN, SDK_DIR, STATE_DIR, OUT_DIR, COUNTER_FILE } = process.env;
const here = new URL(".", import.meta.url).pathname;
const sdkLog = `${STATE_DIR}/sdk.log`;
const children = new Set();
let sdkProcess;
let failures = 0;

// ---------- processes ----------
const start = (command, args, options, log) => {
  const out = openSync(log, "a");
  const child = spawn(command, args, { ...options, stdio: ["ignore", out, out] });
  children.add(child);
  child.on("exit", () => children.delete(child));
  return child;
};
const startServer = () => start(SERVER_BIN, ["--no-logo", "--listen-mode", "tcp", "--bind-ip", "127.0.0.1", "--bind-port", "19923"], {
  cwd: STATE_DIR,
  env: { ...process.env, RESTATE_ADMIN__BIND_ADDRESS: "127.0.0.1:19920", RESTATE_INGRESS__BIND_ADDRESS: "127.0.0.1:19921" }
}, `${STATE_DIR}/server.log`);
const startSdk = async () => {
  const before = sdkLines().length;
  sdkProcess = start("node", [`${here}handlers.mjs`], { env: { ...process.env, SDK_DIR, COUNTER_FILE, SDK_PORT: String(SDK_PORT) } }, sdkLog);
  await until(() => sdkLines().slice(before).some((l) => l.startsWith("SDK-LISTENING")), 10000, "SDK listening");
};
const killSdk = async () => {
  const exited = new Promise((resolve) => sdkProcess.once("exit", resolve));
  const pid = sdkProcess.pid;
  sdkProcess.kill("SIGKILL");
  await exited;
  console.log(`  SDK process ${pid} exited at ${new Date().toISOString()}`);
};
const stopAll = async () => {
  for (const child of children) child.kill("SIGKILL");
  await sleep(300);
};
process.on("exit", () => { for (const child of children) child.kill("SIGKILL"); });

// ---------- HTTP and queries ----------
const until = async (predicate, timeoutMs, what) => {
  const deadline = Date.now() + timeoutMs;
  for (;;) {
    const value = await predicate();
    if (value) return value;
    if (Date.now() > deadline) throw new Error(`timed out waiting for ${what}`);
    await sleep(100);
  }
};
const json = async (url, init) => {
  const res = await fetch(url, init);
  const body = await res.text();
  return { status: res.status, body: body ? JSON.parse(body) : null };
};
const query = async (sql) => (await json(`${ADMIN}/query`, {
  method: "POST", headers: { "content-type": "application/json", accept: "application/json" }, body: JSON.stringify({ query: sql })
})).body.rows;
const JOURNAL_COLUMNS = "index, entry_type, name, completed, invoked_id, invoked_target, sleep_wakeup_at, promise_name, version, raw_length, appended_at, entry_lite_json, entry_json";
const journal = (inv) => query(`SELECT ${JOURNAL_COLUMNS} FROM sys_journal WHERE id = '${inv}' ORDER BY index`);
const statusOf = async (inv) => (await query(`SELECT id, target, status, retry_count, pinned_service_protocol_version, completion_result, completion_failure, last_failure, last_failure_error_code, last_failure_related_command_type, last_failure_related_command_name FROM sys_invocation WHERE id = '${inv}'`))[0];
const childrenOf = (inv) => query(`SELECT id, target, status, completion_result, completion_failure FROM sys_invocation WHERE invoked_by_id = '${inv}' ORDER BY created_at`);
const send = async (target, body = null) => {
  const res = await json(`${INGRESS}/${target}/send`, { method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify(body) });
  return res.body.invocationId;
};
// Sends a cancel and returns "HTTP <status> at <epoch ms>", the time the request was sent.
const cancel = async (inv) => {
  const at = Date.now();
  const res = await fetch(`${ADMIN}/invocations/${inv}/cancel`, { method: "PATCH" });
  return `${res.status}, sent at ${at}`;
};
const killInvocation = async (inv) => (await fetch(`${ADMIN}/invocations/${inv}/kill`, { method: "PATCH" })).status;
const completed = async (inv, timeoutMs = 30000) => until(async () => {
  const s = await statusOf(inv);
  return s?.status === "completed" ? s : null;
}, timeoutMs, `${inv} to complete`);

// ---------- SDK log ----------
const sdkLines = () => {
  try {
    return readFileSync(sdkLog, "utf8").split("\n");
  } catch {
    return [];
  }
};
const linesOf = (inv) => sdkLines().filter((l) => l.includes(inv));
const events = (inv) => sdkLines().filter((l) => l.startsWith(`EVENT ${inv} `)).map((l) => JSON.parse(l.slice(`EVENT ${inv} `.length)));
const lastEvent = (inv, step) => events(inv).filter((e) => e.step === step).at(-1);
const attemptsOf = (inv) => sdkLines().filter((l) => l.startsWith("ATTEMPT ") && l.endsWith(` ${inv}`)).length;
const actionsOf = (inv, name) => sdkLines().filter((l) => l.startsWith(`ACTION ${inv} ${name} `)).length;
// One log record per line that starts a record; continuation lines (stack traces, error details)
// belong to the record above them, which carries the invocation id.
const records = () => sdkLines().reduce((out, line) => {
  if (/^(\[restate\]|ATTEMPT |EVENT |ACTION |SDK-)/.test(line) || out.length === 0) out.push([line]);
  else out.at(-1).push(line);
  return out;
}, []);
const mismatchRecords = (inv) => records().filter((r) => r[0].includes(inv) && r.some((l) => l.includes("(570) Found a mismatch")));
const mismatchLines = (inv) => mismatchRecords(inv).map((r) => r.filter((l) => /\(570\)|mismatch happened|^- /.test(l)).join(" | "));
const waitEvent = (inv, step, timeoutMs = 20000) => until(() => lastEvent(inv, step), timeoutMs, `event ${step} of ${inv}`);

// ---------- journals ----------
const lite = (row) => JSON.parse(row.entry_lite_json ?? "null");
const commands = (rows) => rows.filter((r) => r.entry_type.startsWith("Command: "));
const callsOf = (rows) => rows.filter((r) => r.entry_type === "Command: Call").map((r) => ({ index: r.index, id: lite(r).Command.Call.invocation_id, result: lite(r).Command.Call.result_completion_id }));
const sendSignalsOf = (rows) => rows.filter((r) => r.entry_type === "Command: SendSignal").map((r) => ({ index: r.index, target: lite(r).Command.SendSignal.target_invocation_id, signal: lite(r).Command.SendSignal.signal_id }));
const signalNotifications = (rows) => rows.filter((r) => r.entry_type === "Notification: Signal");
const completionIndex = (rows, completionId) => rows.find((r) => r.entry_type.startsWith("Notification: ") && lite(r).Notification?.id?.CompletionId === completionId)?.index;
const dump = async (fixture, variant, label, inv) => {
  const asked = Date.now();
  const rows = await journal(inv);
  const answered = Date.now();
  mkdirSync(`${OUT_DIR}/journals`, { recursive: true });
  writeFileSync(`${OUT_DIR}/journals/${fixture}-${variant}-${label}.jsonl`, rows.map((r) => JSON.stringify({ invocation: inv, ...r })).join("\n") + "\n");
  console.log(`  journal ${fixture}-${variant}-${label} (${inv}), queried at ${new Date(asked).toISOString()} in ${answered - asked} ms:`);
  for (const r of rows) console.log(`    ${r.index} ${r.entry_type}${r.name ? ` "${r.name}"` : ""} ${r.entry_lite_json}`);
  return rows;
};
const showStatus = async (inv) => {
  const s = await statusOf(inv);
  console.log(`  status ${JSON.stringify(s)}`);
  return s;
};
const showChildren = async (inv) => {
  const rows = await childrenOf(inv);
  for (const r of rows) console.log(`  child ${JSON.stringify(r)}`);
  return rows;
};
const showEvents = (inv) => {
  for (const e of events(inv)) console.log(`  event ${JSON.stringify(e)}`);
};

// ---------- verdicts ----------
const verdict = (name, check) => {
  if (!check.ok) failures++;
  console.log(`RESULT ${name} ${check.ok ? "PASS" : "FAIL"}: ${check.reason}`);
};
// A negative control passes when its check fails; a control that does not fail is a finding.
const control = (name, check) => {
  if (check.ok) failures++;
  console.log(`CONTROL ${name} ${check.ok ? "DID NOT FAIL (finding)" : "FAILS AS REQUIRED"}: ${check.reason}`);
};
const all = (parts) => {
  const bad = parts.filter(([ok]) => !ok).map(([, why]) => why);
  return { ok: bad.length === 0, reason: bad.length === 0 ? parts.map(([, why]) => why).join("; ") : `failed: ${bad.join("; ")}` };
};


// ---------- idempotency-key helpers (rev6-idem) ----------
// The counter file holds one line per handler-body entry ("BODY <label> <inv>") and per execution of
// a counted ctx.run action ("APPLY <label> <inv> <step>"); the handlers append to it directly.
const counterLines = () => {
  try {
    return readFileSync(COUNTER_FILE, "utf8").split("\n").filter(Boolean);
  } catch {
    return [];
  }
};
const bodiesOf = (label) => counterLines().filter((l) => l.startsWith(`BODY ${label} `));
const appliesOf = (label, step = "apply") => counterLines().filter((l) => l.startsWith(`APPLY ${label} `) && l.endsWith(` ${step}`));
const bodyInvocations = (label) => [...new Set(bodiesOf(label).map((l) => l.split(" ")[2]))];
// A request-response ingress call with an idempotency-key header; never throws on HTTP errors.
const ingressCall = async (target, body, key) => {
  const at = Date.now();
  const res = await fetch(`${INGRESS}/${target}`, {
    method: "POST",
    headers: { "content-type": "application/json", ...(key ? { "idempotency-key": key } : {}) },
    body: JSON.stringify(body)
  });
  const text = await res.text();
  return { status: res.status, body: text, id: res.headers.get("x-restate-id"), sentAt: at, ms: Date.now() - at };
};
// Admin cancel and kill that keep the response body, so a 404 or 409 can be quoted.
const adminTerminate = async (inv, verb) => {
  const at = Date.now();
  const res = await fetch(`${ADMIN}/invocations/${inv}/${verb}`, { method: "PATCH" });
  return { status: res.status, body: await res.text(), sentAt: at };
};
const byKey = (key) => query(`SELECT id, target, status, idempotency_key, invoked_by, invoked_by_id, completion_result, completion_failure, created_at, completed_at FROM sys_invocation WHERE idempotency_key = '${key}' ORDER BY created_at`);
const invocationRow = async (inv) => (await query(`SELECT id, target, status, idempotency_key, invoked_by_id, completion_result, completion_failure, completed_at FROM sys_invocation WHERE id = '${inv}'`))[0] ?? null;
const dumpQuiet = async (fixture, variant, label, inv) => {
  const rows = await journal(inv);
  mkdirSync(`${OUT_DIR}/journals`, { recursive: true });
  writeFileSync(`${OUT_DIR}/journals/${fixture}-${variant}-${label}.jsonl`, rows.map((r) => JSON.stringify({ invocation: inv, ...r })).join("\n") + "\n");
  console.log(`  journal ${fixture}-${variant}-${label} (${inv}): ${rows.map((r) => `${r.index}:${r.entry_type.replace(/^(Command|Notification): /, "")}${r.name ? `(${r.name})` : ""}`).join(" ")}`);
  return rows;
};

const failureCount = () => failures;

export { adminTerminate, appliesOf, bodiesOf, bodyInvocations, byKey, counterLines, dumpQuiet, ingressCall, invocationRow, ADMIN, INGRESS, all, failureCount, json, sdkLines, startServer, stopAll, SDK_PORT, actionsOf, attemptsOf, callsOf, cancel, childrenOf, commands, completed, completionIndex, control, dump, events, journal, killInvocation, killSdk, lastEvent, linesOf, mismatchLines, query, send, sendSignalsOf, showChildren, showEvents, showStatus, signalNotifications, startSdk, statusOf, until, verdict, waitEvent };
