// A local HTTP server for R4: answers each request after 10 s and logs
// when it answered, or that the client went away first.
// Lines: RECV|SENT|GONE <x-run header> <ms>.
import http from "node:http";

const port = Number(process.env.SLOW_PORT ?? 19934);
const delayMs = 10_000;
const log = (what, request) =>
  console.log(what, request.headers["x-run"] ?? "-", Date.now());

const answer = (request, response) => () => {
  if (response.destroyed || request.socket.destroyed) return;
  log("SENT", request);
  response.end(`answered ${Date.now()}`);
};
const onRequest = (request, response) => {
  log("RECV", request);
  response.on("close", () => {
    if (!response.writableEnded) log("GONE", request);
  });
  setTimeout(answer(request, response), delayMs);
};
http.createServer(onRequest).listen(port, "127.0.0.1", () =>
  console.log("LISTENING", port));
