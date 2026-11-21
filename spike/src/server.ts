import { createServer } from "node:http2"
import { Layer } from "effect"
import { HttpRouter } from "effect/http"
import { NodeHttpServer, NodeRuntime } from "@effect/platform-node"
import { Restate } from "@t0ster/restate-effect"
import { SpikeLive } from "./app.ts"

SpikeLive.pipe(
  Layer.provide(Restate.layerHttp),
  layer => HttpRouter.serve(layer, { disableLogger: true }),
  Layer.provide(NodeHttpServer.layer(() => createServer(), { port: Number(process.env.PORT ?? 9080), host: "127.0.0.1" })),
  Layer.launch,
  NodeRuntime.runMain
)
