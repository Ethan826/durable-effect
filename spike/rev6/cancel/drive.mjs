// Runs the rev6-cancel and rev6-replay-checks fixtures against a local Restate server: starts the
// server and the SDK process (handlers.mjs), drives each fixture, dumps journals as JSON lines and
// prints one RESULT line per fixture and one CONTROL line per negative control.
// Environment (set by run.sh): SERVER_BIN, SDK_DIR, STATE_DIR, OUT_DIR, FIXTURES.
import { mkdirSync } from "node:fs";
import { setTimeout as sleep } from "node:timers/promises";
import * as d from "./lib.mjs";
import * as fixtures from "./fixtures.mjs";

const { ADMIN, SDK_PORT } = d;
let harnessFailed = false;

const main = async () => {
  mkdirSync(process.env.STATE_DIR, { recursive: true });
  d.startServer();
  await d.until(async () => (await fetch(`${ADMIN}/health`).catch(() => null))?.ok, 20000, "server health");
  await d.startSdk();
  for (const uri of [`http://127.0.0.1:${SDK_PORT}`, `http://127.0.0.1:${SDK_PORT}/codec`]) {
    const res = await d.json(`${ADMIN}/deployments`, { method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify({ uri }) });
    console.log(`deployment ${uri}: HTTP ${res.status} protocol versions ${res.body?.min_protocol_version}..${res.body?.max_protocol_version} services ${res.body?.services?.map((s) => s.name).join(",")}`);
  }
  const only = (process.env.FIXTURES ?? "F12,F13,F14,F15,F16,F20").split(",");
  for (const name of only) await fixtures[name]({ restartSdk: async () => { await d.killSdk(); await sleep(1000); await d.startSdk(); } });
  await sleep(500);
  console.log(`\nSDK log WARN/ERROR lines: ${d.sdkLines().filter((l) => /WARN|ERROR/.test(l)).length}`);
};

try {
  await main();
} catch (e) {
  harnessFailed = true;
  console.log(`RESULT harness FAIL: ${e.stack}`);
} finally {
  await d.stopAll();
  const failures = d.failureCount() + (harnessFailed ? 1 : 0);
  console.log(`\n${failures === 0 ? "ALL PASS" : `${failures} FAILURE(S)`} (fixtures and controls)`);
  process.exitCode = failures === 0 ? 0 : 1;
}
