#!/bin/bash
# Runs handler.mjs against a local Restate server and prints each scenario's result and attempts.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
server="$here/../node_modules/@restatedev/restate-server-darwin-arm64/bin/restate-server"
state=$(mktemp -d)
cleanup() { kill "${sdk_pid:-}" "${server_pid:-}" 2>/dev/null || true; rm -rf "$state"; }
trap cleanup EXIT
(cd "$here/.." && exec node abandonment/handler.mjs) > "$state/sdk.log" 2>&1 & sdk_pid=$!
(cd "$state" && exec env RESTATE_ADMIN__BIND_ADDRESS=127.0.0.1:19890 RESTATE_INGRESS__BIND_ADDRESS=127.0.0.1:19891 \
  "$server" --no-logo --listen-mode tcp --bind-ip 127.0.0.1 --bind-port 19893) > "$state/server.log" 2>&1 & server_pid=$!
for _ in $(seq 1 40); do curl -fsS http://127.0.0.1:19890/health >/dev/null 2>&1 && break; sleep .25; done
curl -fsS -H 'Content-Type: application/json' -d '{"uri":"http://127.0.0.1:19892"}' http://127.0.0.1:19890/deployments > /dev/null
for h in unsubscribed subscribedLonger subscribedShorter combined returnsWithPending returnsAtOnce; do
  printf '%s result ' "$h"; curl -sS --max-time 30 -H 'Content-Type: application/json' -d 'null' "http://127.0.0.1:19891/Abandon/$h"; echo
done
sleep 5
grep -E "ATTEMPT|old |awaitNext|WARN|Replaying" "$state/sdk.log" | sed -E 's/\[restate\]\[[^]]*\]//; s/\[inv_[^]]*\]//'
