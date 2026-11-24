// Runs every rev6-open invocation (O1 to O3, issue #48 step 7) in turn
// and records what the server holds for each: out/manifest.json lists
// the invocations, journals/ holds their journals. check.mjs judges.
import { writeFileSync } from "node:fs";
import { join } from "node:path";
import {
  send, statusOf, sleep, waitDone, kill, cancel, dumpJournal
} from "./drive-lib.mjs";

const out = join(import.meta.dirname, "out");

// [fixture, variant, service, handler, count, cancel after ms or null,
// watch ms]. An invocation still running when its watch ends is dumped
// and then killed.
const plan = [
  ["O1", "main", "OpenOrder", "o1", 2, 1_000, 20_000],
  ["O2", "gate", "OpenGate", "o2Gate", 2, 600, 20_000],
  ["O2", "nogate", "OpenGate", "o2NoGate", 2, 600, 20_000],
  ["O3", "okFreeze", "OpenFreeze", "o3OkFreeze", 2, null, 20_000],
  ["O3", "okNoFreeze", "OpenFreeze", "o3OkNoFreeze", 2, null, 20_000],
  ["O3", "termFreeze", "OpenFreeze", "o3TermFreeze", 2, null, 20_000],
  ["O3", "termRetryableFirst", "OpenFreeze", "o3TermRetryableFirst", 2,
    null, 20_000]
];

const manifest = [];
const record = async (fixture, variant, k, id, journals) => {
  const status = await statusOf(id);
  manifest.push({ fixture, variant, k, id, status, journals });
  console.log(fixture, variant, k, id, status?.status,
    status?.completion_result ?? "", status?.retry_count ?? "");
};

const cancelLater = async (id, ms) => {
  if (ms === null) return;
  await sleep(ms);
  console.log("cancel", id, await cancel(id));
};

const runOne = async (step, k) => {
  const [fixture, variant, service, handler, , cancelAt, watch] = step;
  const id = await send(service, handler);
  await cancelLater(id, cancelAt);
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
  await sleep(6_000);
  writeFileSync(join(out, "manifest.json"), JSON.stringify(manifest, null, 1));
};

await main();
