// Runs every rev6-order and rev6-effects fixture invocation in turn and
// records what the server holds for each: out/manifest.json lists the
// invocations, journals/ holds their journals, out/protocol.json the
// deployment's and invocations' protocol versions. check.mjs judges.
import { writeFileSync } from "node:fs";
import { join } from "node:path";
import {
  query, send, statusOf, childrenOf, sleep, waitDone, kill, dumpJournal
} from "./drive-lib.mjs";

const out = join(import.meta.dirname, "out");

// [fixture, variant, service, handler, count]
const plan = [
  ["F1", "main", "Order", "f1", 10],
  ["F1", "changed", "Order", "f1Changed", 3],
  ["F2", "main", "Order", "f2", 3],
  ["F2", "reversed", "Order", "f2Reversed", 3],
  ["F2", "main-live", "OrderLive", "f2", 3],
  ["F2", "reversed-live", "OrderLive", "f2Reversed", 3],
  ["F3", "dropped", "OrderLive", "f3Dropped", 1],
  ["F4", "main", "Order", "f4", 2],
  ["F4", "subscribed", "Order", "f4Subscribed", 2],
  ["F5", "live", "FlowLive", "f5", 2], ["F5", "replay", "Flow", "f5", 2],
  ["F5", "subscribedLonger", "FlowLive", "subscribedLonger", 1],
  ["F6", "call-live", "FlowLive", "f6call", 1],
  ["F6", "run-live", "FlowLive", "f6run", 1],
  ["F6", "awk-live", "FlowLive", "f6awk", 1],
  ["F6", "retry-live", "FlowLive", "f6retry", 1],
  ["F6", "call-replay", "Flow", "f6call", 1],
  ["F6", "run-replay", "Flow", "f6run", 1],
  ["F6", "awk-replay", "Flow", "f6awk", 1],
  ["F6", "retry-replay", "Flow", "f6retry", 1],
  ["F7", "returnsWithPending", "FlowLive", "returnsWithPending", 1],
  ["F8", "main", "FlowLive", "f8", 2],
  ["F8", "atOnce", "FlowLive", "f8AtOnce", 2],
  ["F9", "replay", "Order", "f9", 3], ["F9", "live", "OrderLive", "f9", 3],
  ["F10", "main", "OrderLive", "f10", 20],
  ["F17", "main", "Effects", "f17", 2],
  ["F17", "keep", "Effects", "f17Keep", 2],
  ["F18", "unraced-replay", "Effects", "f18Unraced", 1],
  ["F18", "beside-replay", "Effects", "f18Beside", 1],
  ["F18", "besideTaken-replay", "Effects", "f18BesideTaken", 1],
  ["F18", "alone-replay", "Effects", "f18Alone", 1],
  ["F18", "unraced-live", "EffectsLive", "f18Unraced", 1],
  ["F18", "beside-live", "EffectsLive", "f18Beside", 1],
  ["F18", "besideTaken-live", "EffectsLive", "f18BesideTaken", 1],
  ["F18", "alone-live", "EffectsLive", "f18Alone", 1],
  ["F19", "main", "EffectsLive", "f19", 1],
  ["F19", "terminal", "EffectsLive", "f19Terminal", 1]
];

const manifest = [];
const record = async (fixture, variant, k, id, journals) => {
  const status = await statusOf(id);
  const children = await childrenOf(id);
  manifest.push({ fixture, variant, k, id, status, children, journals });
  console.log(fixture, variant, k, id, status?.status,
    status?.completion_result ?? "", status?.retry_count ?? "");
};

// One invocation that should complete: wait, then dump its journal.
const runOne = async ([fixture, variant, service, handler], k) => {
  const id = await send(service, handler);
  await waitDone(id, 30_000);
  const file = await dumpJournal(id, `${fixture}-${variant}.${k}-final.jsonl`);
  await record(fixture, variant, k, id, [file]);
};

// F3's main case never completes: observe 4 s of attempts, then kill.
const runReplacedRace = async () => {
  const id = await send("OrderLive", "f3");
  await sleep(4000);
  const file = await dumpJournal(id, "F3-main.1-atkill.jsonl");
  await record("F3", "main", 1, id, [file]);
  console.log("F3 main kill HTTP", await kill(id));
};

// F7: dump at completion and again after the call and run would finish.
const runReturnsMidRace = async () => {
  const id = await send("FlowLive", "f7");
  await waitDone(id, 30_000);
  const first = await dumpJournal(id, "F7-main.1-final.jsonl");
  await sleep(3000);
  const late = await dumpJournal(id, "F7-main.1-late.jsonl");
  await record("F7", "main", 1, id, [first, late]);
};

const protocolInfo = async () => ({
  deployments: await query(`SELECT id, endpoint,
    min_service_protocol_version, max_service_protocol_version
    FROM sys_deployment`),
  pinned: await query(`SELECT pinned_service_protocol_version AS v,
    COUNT(*) AS n FROM sys_invocation GROUP BY v`)
});

const main = async () => {
  await runReplacedRace();
  await runReturnsMidRace();
  for (const step of plan) {
    for (let k = 1; k <= step[4]; k += 1) await runOne(step, k);
  }
  await sleep(3000);
  writeFileSync(join(out, "manifest.json"), JSON.stringify(manifest, null, 1));
  writeFileSync(join(out, "protocol.json"),
    JSON.stringify(await protocolInfo(), null, 1));
};

await main();
