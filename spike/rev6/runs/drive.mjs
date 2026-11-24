// Runs every rev6-runs invocation (R1 to R4, issue #48) in turn and
// records what the server holds for each: out/manifest.json lists the
// invocations, journals/ holds their journals. check.mjs judges.
import { writeFileSync } from "node:fs";
import { join } from "node:path";
import {
  send, statusOf, sleep, waitDone, kill, dumpJournal
} from "./drive-lib.mjs";

const out = join(import.meta.dirname, "out");

// [fixture, variant, service, handler, count]; Runs forces replay.
const plan = [
  ["R1", "keep-live", "RunsLive", "r1Keep", 2],
  ["R1", "keep-replay", "Runs", "r1Keep", 2],
  ["R1", "drop-live", "RunsLive", "r1Drop", 1],
  ["R1", "drop-replay", "Runs", "r1Drop", 1],
  ["R2", "wait-live", "RunsLive", "r2Wait", 2],
  ["R2", "wait-replay", "Runs", "r2Wait", 2],
  ["R2", "return-live", "RunsLive", "r2Return", 1],
  ["R2", "return-replay", "Runs", "r2Return", 1],
  ["R3", "hold-live", "RunsLive", "r3Hold", 2],
  ["R3", "hold-replay", "Runs", "r3Hold", 2],
  ["R3", "settled-live", "RunsLive", "r3HoldSettled", 2],
  ["R3", "settled-replay", "Runs", "r3HoldSettled", 2],
  ["R3", "nohold-live", "RunsLive", "r3NoHold", 1],
  ["R3", "nohold-replay", "Runs", "r3NoHold", 1],
  ["R4", "main", "RunsLive", "r4", 2],
  ["R4", "noabort", "RunsLive", "r4NoAbort", 1]
];

const manifest = [];
const record = async (fixture, variant, k, id, journals) => {
  const status = await statusOf(id);
  manifest.push({ fixture, variant, k, id, status, journals });
  console.log(fixture, variant, k, id, status?.status,
    status?.completion_result ?? "", status?.retry_count ?? "");
};

// Variants watched longer: R3 hold-replay stalled for over 30 s in the
// first run; watch it past the server's abort timeout.
const patience = { "hold-replay": 90_000 };

// One invocation that should complete: wait, then dump its journal.
const runOne = async ([fixture, variant, service, handler], k) => {
  const id = await send(service, handler);
  await waitDone(id, patience[variant] ?? 30_000);
  await sleep(500);
  const file = await dumpJournal(id, `${fixture}-${variant}.${k}.jsonl`);
  await record(fixture, variant, k, id, [file]);
};

// R4 control A retries without end: watch 5 s, dump, then kill.
const runNoConvert = async () => {
  const id = await send("RunsLive", "r4NoConvert");
  await sleep(5000);
  const file = await dumpJournal(id, "R4-noconvert.1-atkill.jsonl");
  await record("R4", "noconvert", 1, id, [file]);
  console.log("R4 noconvert kill HTTP", await kill(id));
};

const main = async () => {
  for (const step of plan) {
    for (let k = 1; k <= step[4]; k += 1) await runOne(step, k);
  }
  await runNoConvert();
  await sleep(11_000);
  writeFileSync(join(out, "manifest.json"), JSON.stringify(manifest, null, 1));
};

await main();
