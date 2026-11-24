// Serves the rev6-open fixtures (O1 to O3, issue #48 step 7) on port
// 19952. The SDK comes from RESTATE_SDK_DIR (a node_modules directory)
// when set. Adapted from ../rerun/serve.mjs.
import http2 from "node:http2";
import { readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { join } from "node:path";
import { pathToFileURL } from "node:url";
import {
  openHandlers, replayOptions, gateOptions, liveOptions
} from "./open.mjs";

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

const all = openHandlers(sdk);
const pick = (names) =>
  Object.fromEntries(names.map((name) => [name, all[name]]));

const services = [
  sdk.service({ name: "OpenOrder", handlers: pick(["o1"]),
    options: replayOptions }),
  sdk.service({ name: "OpenGate", handlers: pick(["o2Gate", "o2NoGate"]),
    options: gateOptions }),
  sdk.service({ name: "OpenFreeze", handlers: pick(["o3OkFreeze",
    "o3OkNoFreeze", "o3TermFreeze", "o3TermRetryableFirst"]),
    options: liveOptions })
];
const handler = services
  .reduce((endpoint, service) => endpoint.bind(service), sdk.endpoint())
  .http2Handler();
http2.createServer(handler).listen(19952, "127.0.0.1", () =>
  console.log("LISTENING 19952"));
