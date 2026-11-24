#!/bin/bash
# Runs the rev6-idem fixtures (A39 to A42 of the assumptions register on #48): idempotency keys of
# cancelled and killed invocations, kill during compensation, cancel after completion, a third
# cancel. Ports: admin 19920, ingress 19921, SDK 19922, server node 19923.
#
# RESTATE_SERVER_VERSION and RESTATE_SDK_VERSION choose the versions under test (defaults are the
# pinned ones). A version other than the one in spike/node_modules is looked up in
# $here/versions/<package>@<version>/node_modules; the script prints the install command if it is
# missing. GROUPS limits the fixture groups (default G1,G2,G3,G4,G5,G6). The counter file the
# handlers append to (outside the journal) is $here/counters.txt, rewritten on every run.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
spike="$here/../.."
server_version=${RESTATE_SERVER_VERSION:-1.8.1}
sdk_version=${RESTATE_SDK_VERSION:-1.18.4}

# Prints the node_modules directory holding <package> at <version>, or fails with the install hint.
modules_for() {
  local package=$1 version=$2 dir
  for dir in "$spike/node_modules" "$here/versions/$package@$version/node_modules"; do
    if [ -f "$dir/$package/package.json" ] && [ "$(jq -r .version "$dir/$package/package.json")" = "$version" ]; then
      echo "$dir"; return 0
    fi
  done
  echo "missing $package@$version; install it with:" >&2
  echo "  npm install --prefix '$here/versions/$package@$version' --save-exact '$package@$version'" >&2
  return 1
}
server_modules=$(modules_for @restatedev/restate-server-darwin-arm64 "$server_version")
sdk_modules=$(modules_for @restatedev/restate-sdk "$sdk_version")
export SERVER_BIN="$server_modules/@restatedev/restate-server-darwin-arm64/bin/restate-server"
export SDK_DIR="$sdk_modules/@restatedev/restate-sdk"
export OUT_DIR="$here"
export COUNTER_FILE="$here/counters.txt"
: > "$COUNTER_FILE"
STATE_DIR=$(mktemp -d)
export STATE_DIR

# Kills anything still listening on this harness's ports, then removes the server's state.
cleanup() {
  local pids
  pids=$(lsof -t -iTCP:19920-19923 -sTCP:LISTEN 2>/dev/null || true)
  if [ -n "$pids" ]; then echo "cleanup: killing leftover $pids"; kill -9 $pids 2>/dev/null || true; fi
  rm -rf "$STATE_DIR"
}
trap cleanup EXIT

echo "== versions: $("$SERVER_BIN" --version), restate-sdk $(jq -r .version "$SDK_DIR/package.json"), node $(node --version)"
echo "== started $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo
echo "== live fixtures"
live_status=0
node "$here/drive.mjs" || live_status=$?
echo
echo "== exit: live $live_status"
[ "$live_status" -eq 0 ]
