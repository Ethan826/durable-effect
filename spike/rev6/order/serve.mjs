// Serves the rev6-order and rev6-effects fixtures on port 19902. The SDK
// comes from RESTATE_SDK_DIR (a node_modules directory) when set, so the
// same fixtures can run against another SDK version. Each request's
// content type is logged: it carries the negotiated protocol version.
import http2 from "node:http2";
import { readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { join } from "node:path";
import { pathToFileURL } from "node:url";
import { orderServices } from "./order.mjs";
import { flowServices } from "./flow.mjs";
import { effectServices } from "./effects.mjs";

const sdkName = "@restatedev/restate-sdk";
const sdkDir = process.env.RESTATE_SDK_DIR;

// The SDK's own package.json, found from the module that was loaded.
const packageOf = (entry) => {
  const root = entry.slice(0, entry.lastIndexOf("/dist/"));
  return JSON.parse(readFileSync(join(root, "package.json"), "utf8"));
};
const resolveEntry = () =>
  createRequire(join(sdkDir ?? import.meta.dirname, "x.js"))
    .resolve(sdkName);

const entry = resolveEntry();
const sdk = await import(pathToFileURL(entry).href);
console.log("SDK_VERSION", packageOf(entry).version, entry);

const services = [
  ...orderServices(sdk), ...flowServices(sdk), ...effectServices(sdk)
];
const handler = services
  .reduce((endpoint, service) => endpoint.bind(service), sdk.endpoint())
  .http2Handler();
const logged = (request, response) => {
  const type = request.headers["content-type"] ?? "-";
  console.log("REQ", request.url, type);
  handler(request, response);
};
http2.createServer(logged).listen(19902, "127.0.0.1", () =>
  console.log("LISTENING 19902"));
