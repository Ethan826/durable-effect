// Serves the rev6-runs fixtures (R1 to R4, issue #48) on port 19932. The
// SDK comes from RESTATE_SDK_DIR (a node_modules directory) when set, so
// the same fixtures can run against another SDK version.
import http2 from "node:http2";
import { readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { join } from "node:path";
import { pathToFileURL } from "node:url";
import { runHandlers } from "./runs.mjs";
import { abortHandlers } from "./abort.mjs";
import { retention, replayOptions } from "./lib.mjs";

const sdkName = "@restatedev/restate-sdk";
const sdkDir = process.env.RESTATE_SDK_DIR;

// The SDK's own package.json, found from the module that was loaded.
const packageOf = (entry) => {
  const root = entry.slice(0, entry.lastIndexOf("/dist/"));
  return JSON.parse(readFileSync(join(root, "package.json"), "utf8"));
};
const entry = createRequire(join(sdkDir ?? import.meta.dirname, "x.js"))
  .resolve(sdkName);
const sdk = await import(pathToFileURL(entry).href);
console.log("SDK_VERSION", packageOf(entry).version, entry);

const handlers = { ...runHandlers(sdk), ...abortHandlers(sdk) };
const services = [
  sdk.service({ name: "Runs", handlers, options: replayOptions }),
  sdk.service({ name: "RunsLive", handlers, options: retention })
];
const handler = services
  .reduce((endpoint, service) => endpoint.bind(service), sdk.endpoint())
  .http2Handler();
http2.createServer(handler).listen(19932, "127.0.0.1", () =>
  console.log("LISTENING 19932"));
