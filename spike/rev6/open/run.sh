#!/bin/bash
# Runs the rev6-open fixtures O1 to O3 (issue #48, step 7: the open items of the
# adversarial review of revision 6, comment 7144035354)
# against a local Restate server and prints PASS or FAIL per
# fixture. Ports: admin 19950, ingress 19951, SDK 19952, server 19953.
# SDK_VERSION and SERVER_VERSION select the versions under test; the pinned
# ones are the defaults. Another version is installed under .versions/.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
spike="$here/../.."
SDK_VERSION=${SDK_VERSION:-1.18.4}
SERVER_VERSION=${SERVER_VERSION:-1.8.1}
platform=restate-server-darwin-arm64

# The node_modules directory that holds a package at the wanted version.
modules_for() { # package version
  local installed="$spike/node_modules/$1/package.json"
  if [ "$(jq -r .version "$installed")" = "$2" ]; then
    echo "$spike/node_modules"; return
  fi
  local prefix="$here/.versions/$(basename "$1")-$2"
  [ -d "$prefix/node_modules/$1" ] ||
    npm install --prefix "$prefix" --no-save --save-exact "$1@$2" >&2
  echo "$prefix/node_modules"
}
sdk_dir=$(modules_for @restatedev/restate-sdk "$SDK_VERSION")
server_dir=$(modules_for @restatedev/restate-server "$SERVER_VERSION")
server="$server_dir/@restatedev/$platform/bin/restate-server"

out="$here/out"
state=$(mktemp -d)
mkdir -p "$here/journals" "$out"
rm -f "$here"/journals/*.jsonl "$out"/*
cleanup() {
  kill "${sdk_pid:-}" "${server_pid:-}" 2>/dev/null || true
  wait 2>/dev/null || true
  rm -rf "$state"
}
trap cleanup EXIT
EFFECTS_FILE="$out/effects.log" RESTATE_SDK_DIR="$sdk_dir" \
  node "$here/serve.mjs" > "$out/sdk.log" 2>&1 & sdk_pid=$!
(cd "$state" && exec env \
  RESTATE_ADMIN__BIND_ADDRESS=127.0.0.1:19950 \
  RESTATE_INGRESS__BIND_ADDRESS=127.0.0.1:19951 \
  "$server" --no-logo --listen-mode tcp --bind-ip 127.0.0.1 \
  --bind-port 19953) > "$out/server.log" 2>&1 & server_pid=$!
for _ in $(seq 1 60); do
  curl -fsS http://127.0.0.1:19950/health >/dev/null 2>&1 && break
  sleep .25
done
curl -fsS -H 'Content-Type: application/json' \
  -d '{"uri":"http://127.0.0.1:19952"}' \
  http://127.0.0.1:19950/deployments > /dev/null
touch "$out/effects.log"

echo "== rev6-open fixtures O1 to O3, issue #48 step 7"
echo "requested SDK $SDK_VERSION, server $SERVER_VERSION"
echo "loaded $(grep -m1 SDK_VERSION "$out/sdk.log")"
echo "server binary: $("$server" --version)"
echo "node $(node --version)"
echo
echo "== Driver"
node "$here/drive.mjs"
echo
echo "== Checks"
node "$here/check.mjs" "$SDK_VERSION" "$SERVER_VERSION" \
  "$("$server" --version)"
