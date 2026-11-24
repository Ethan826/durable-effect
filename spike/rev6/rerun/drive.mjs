// Runs every rev6-rerun invocation (R5, R6, issue #48) in turn and
// records what the server holds for each: out/manifest.json lists the
// invocations, journals/ holds their journals. check.mjs judges.
import { writeFileSync } from "node:fs";
import { join } from "node:path";
import {
  send, statusOf, sleep, waitDone, kill, dumpJournal
} from "./drive-lib.mjs";

const out = join(import.meta.dirname, "out");

// [fixture, variant, service, handler, count, watch ms]. An invocation
// still running when its watch ends is dumped and then killed.
const plan = [
  ["R5", "main", "Rerun", "r5", 2, 30_000],
  ["R5", "fresh", "Rerun", "r5Fresh", 1, 20_000],
  ["R6", "main", "Warn", "r6", 2, 30_000],
  ["R6", "fromsend", "Warn", "r6FromSend", 1, 30_000]
];

const manifest = [];
const record = async (fixture, variant, k, id, journals) => {
  const status = await statusOf(id);
  manifest.push({ fixture, variant, k, id, status, journals });
  console.log(fixture, variant, k, id, status?.status,
    status?.completion_result ?? "", status?.retry_count ?? "");
};

const runOne = async ([fixture, variant, service, handler, , watch], k) => {
  const id = await send(service, handler);
  const row = await waitDone(id, watch);
  await sleep(500);
  const file = await dumpJournal(id, `${fixture}-${variant}.${k}.jsonl`);
  await record(fixture, variant, k, id, [file]);
  if (row?.status !== "completed") {
    console.log(fixture, variant, k, "kill HTTP", await kill(id));
  }
};

const main = async () => {
  for (const step of plan) {
    for (let k = 1; k <= step[4]; k += 1) await runOne(step, k);
  }
  await sleep(11_000);
  writeFileSync(join(out, "manifest.json"), JSON.stringify(manifest, null, 1));
};

await main();
