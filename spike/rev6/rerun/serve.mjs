// Serves the rev6-rerun fixtures (R5, R6, issue #48) on port 19942. The
// SDK comes from RESTATE_SDK_DIR (a node_modules directory) when set.
// Adapted from ../runs/serve.mjs.
import http2 from "node:http2";
import { readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { join } from "node:path";
import { pathToFileURL } from "node:url";
import { rerunHandlers, rerunOptions } from "./rerun.mjs";
import { warnHandlers, warnOptions } from "./warn.mjs";

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

const services = [
  sdk.service({ name: "Rerun", handlers: rerunHandlers(sdk),
    options: rerunOptions }),
  sdk.service({ name: "Warn", handlers: warnHandlers(sdk),
    options: warnOptions })
];
const handler = services
  .reduce((endpoint, service) => endpoint.bind(service), sdk.endpoint())
  .http2Handler();
http2.createServer(handler).listen(19942, "127.0.0.1", () =>
  console.log("LISTENING 19942"));
