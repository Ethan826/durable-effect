#!/bin/sh
# Starts a local Restate server bound to loopback. MODE=replay forces a suspension after every
# await (what the testcontainers alwaysReplay option sets), so each step replays the handler.
cd "$(dirname "$0")/.."
if [ "$MODE" = replay ]; then export RESTATE_WORKER__INVOKER__INACTIVITY_TIMEOUT=0s; fi
export RESTATE_BASE_DIR="data/restate-${MODE:-normal}"
export RESTATE_ADVERTISED_ADDRESS=http://127.0.0.1:5122/
export RESTATE_BIND_ADDRESS=127.0.0.1:5122
export RESTATE_ADMIN__BIND_ADDRESS=127.0.0.1:9070
export RESTATE_INGRESS__BIND_ADDRESS=127.0.0.1:8080
exec node_modules/.bin/restate-server
