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

# F1 and F3 on #46. Everything below runs after the #31 output above, in the same server session.
mark=$(wc -l < "$state/sdk.log")
query() {
  jq -n --arg q "$1" '{query: $q}' \
    | curl -sS -H 'Content-Type: application/json' -H 'Accept: application/json' -d @- http://127.0.0.1:19890/query \
    | jq -c '.rows[]'
}
journal() {
  echo "  journal of $1:"
  query "SELECT index, entry_type, name, completed, invoked_id, invoked_target, entry_lite_json FROM sys_journal WHERE id = '$1' ORDER BY index" | sed 's/^/    /'
}
status() {
  query "SELECT id, target, status, retry_count, completion_result, completion_failure, last_failure FROM sys_invocation WHERE id = '$1'" | sed 's/^/  /'
}
echo
echo "== F1: per-tick race =="
for svc in Race RaceReplay; do
  for h in subscribeControl raceDropLoser raceKeepLoser; do
    headers="$state/headers"
    printf '%s/%s result ' "$svc" "$h"
    curl -sS --max-time 60 -D "$headers" -H 'Content-Type: application/json' -d 'null' "http://127.0.0.1:19891/$svc/$h"; echo
    inv=$(grep -i '^x-restate-id:' "$headers" | awk '{print $2}' | tr -d '\r')
    status "$inv"
    journal "$inv"
  done
done
echo
echo "== F3: cancelling a parent with a child call =="
for svc in Parent ParentReplay; do
  for h in cancelSubscribedCall cancelReleasedCall; do
    inv=$(curl -sS -H 'Content-Type: application/json' -d 'null' "http://127.0.0.1:19891/$svc/$h/send" | jq -r .invocationId)
    echo "$svc/$h invocation $inv"
    sleep 3
    echo " before cancel:"
    status "$inv"
    journal "$inv"
    curl -sS -X PATCH -o /dev/null -w ' cancel request HTTP %{http_code}\n' "http://127.0.0.1:19890/invocations/$inv/cancel"
    sleep 3
    echo " after cancel:"
    status "$inv"
    journal "$inv"
    echo "  child invocations:"
    query "SELECT id, status, retry_count, completion_result, completion_failure FROM sys_invocation WHERE invoked_by_id = '$inv'" | sed 's/^/    /'
  done
done
sleep 2
echo
echo "== SDK log for F1 and F3 =="
tail -n +"$((mark + 1))" "$state/sdk.log" | grep -E "ATTEMPT|TICK|WARN|Error|Replaying|uspend|ancel" | sed -E 's/\[restate\]\[[^]]*\]//; s/\[inv_[^]]*\]//'
