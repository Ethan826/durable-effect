// Runs the rev6-idem fixtures against a local Restate server: starts the server and the SDK
// process (handlers.mjs), registers the deployment, runs each group and prints one RESULT line per
// case and one CONTROL line per negative control.
// Environment (set by run.sh): SERVER_BIN, SDK_DIR, STATE_DIR, OUT_DIR, COUNTER_FILE, GROUPS.
import { copyFileSync, mkdirSync } from "node:fs";
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
  const res = await d.json(`${ADMIN}/deployments`, { method: "POST", headers: { "content-type": "application/json" }, body: JSON.stringify({ uri: `http://127.0.0.1:${SDK_PORT}` }) });
  console.log(`deployment: HTTP ${res.status} protocol versions ${res.body?.min_protocol_version}..${res.body?.max_protocol_version} services ${res.body?.services?.map((s) => s.name).join(",")}`);
  for (const name of ["IdTarget", "IdShort"]) {
    const svc = await d.json(`${ADMIN}/services/${name}`);
    console.log(`service ${name}: idempotency_retention ${svc.body?.idempotency_retention}, journal_retention ${svc.body?.journal_retention}`);
  }
  const version = await d.json(`${ADMIN}/version`);
  console.log(`admin /version: ${JSON.stringify(version.body)}`);
  const only = (process.env.GROUPS ?? "G1,G2,G3,G4,G5,G6,G7,G8").split(",");
  for (const name of only) await fixtures[name]();
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
  try { copyFileSync(`${process.env.STATE_DIR}/sdk.log`, `${process.env.OUT_DIR}/sdk-last.log`); } catch {}
  const failures = d.failureCount() + (harnessFailed ? 1 : 0);
  console.log(`\n${failures === 0 ? "ALL PASS" : `${failures} FAILURE(S)`} (fixtures and controls)`);
  process.exitCode = failures === 0 ? 0 : 1;
}
