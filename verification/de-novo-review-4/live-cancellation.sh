#!/bin/bash
set -euo pipefail
server=/Users/ethan/Desktop/durable-effect/spike/node_modules/@restatedev/restate-server-darwin-arm64/bin/restate-server
state=$(mktemp -d /tmp/durable-live.XXXXXX)
sdk_pid=
server_pid=
cleanup() {
  if [ -n "$sdk_pid" ]; then kill "$sdk_pid" 2>/dev/null || true; fi
  if [ -n "$server_pid" ]; then kill "$server_pid" 2>/dev/null || true; fi
}
trap cleanup EXIT
node live-cancellation.mjs > live-sdk.log 2>&1 &
sdk_pid=$!
(
  cd "$state"
  exec env RESTATE_ADMIN__BIND_ADDRESS=127.0.0.1:19870 RESTATE_INGRESS__BIND_ADDRESS=127.0.0.1:19880 RESTATE_WORKER__INVOKER__INACTIVITY_TIMEOUT="${1:-1m}" "$server" --no-logo --listen-mode tcp --bind-ip 127.0.0.1 --bind-port 19871
) > live-server.log 2>&1 &
server_pid=$!
admin=http://127.0.0.1:19870
ingress=http://127.0.0.1:19880
ready=no
for trial in {1..30}; do
  if curl -fsS "$admin/health" >/dev/null 2>&1; then ready=yes; break; fi
  if ! kill -0 "$server_pid" 2>/dev/null; then cat live-server.log; exit 1; fi
  sleep .25
done
if [ "$ready" != yes ]; then cat live-server.log; exit 1; fi
curl -fsS --max-time 8 -H 'Content-Type: application/json' -d '{"uri":"http://127.0.0.1:19882"}' "$admin/deployments"
printf '\nreplay '
curl -fsS --max-time 7 -H 'Content-Type: application/json' -d 'null' "$ingress/DurableReview/replay"
printf '\nwrap '
curl -fsS --max-time 8 -H 'Content-Type: application/json' -d 'null' "$ingress/DurableReview/wrap"
for scenario in wait sample two:unsubscribed two:subscribed; do
  handler="${scenario%%:*}"
  case "$scenario" in
    two:unsubscribed) data=false ;;
    two:subscribed) data=true ;;
    *) data=null ;;
  esac
  response=$(curl -fsS --max-time 4 -H 'Content-Type: application/json' -d "$data" "$ingress/DurableReview/$handler/send")
  id=$(node -p 'JSON.parse(process.argv[1]).invocationId' "$response")
  sleep .5
  printf '\n%s cancel ' "$scenario"
  curl -fsS --max-time 4 -X DELETE "$admin/invocations/$id"
  printf '\n%s result ' "$scenario"
  curl -sS --max-time 6 "$ingress/restate/invocation/$id/attach" || true
  printf '\n'
done
cat live-sdk.log
