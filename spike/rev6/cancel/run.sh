#!/bin/bash
# Runs the rev6-cancel (F12 to F16, A5) and rev6-replay-checks (F20) fixtures of the assumptions
# register on #48. Ports: admin 19910, ingress 19911, SDK 19912, server node 19913.
#
# RESTATE_SERVER_VERSION and RESTATE_SDK_VERSION choose the versions under test (defaults are the
# pinned ones). A version other than the one in spike/node_modules is looked up in
# $here/versions/<package>@<version>/node_modules; the script prints the install command if it is
# missing. FIXTURES limits the live fixtures (default F12,F13,F14,F15,F16,F20).
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
STATE_DIR=$(mktemp -d)
export STATE_DIR

# Kills anything still listening on this harness's ports, then removes the server's state.
cleanup() {
  local pids
  pids=$(lsof -t -iTCP:19910-19913 -sTCP:LISTEN 2>/dev/null || true)
  if [ -n "$pids" ]; then echo "cleanup: killing leftover $pids"; kill -9 $pids 2>/dev/null || true; fi
  rm -rf "$STATE_DIR"
}
trap cleanup EXIT

echo "== versions: $("$SERVER_BIN" --version), restate-sdk $(jq -r .version "$SDK_DIR/package.json"), node $(node --version)"
echo "== started $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo
echo "== A5: scripted test against the SDK's wasm VM"
a5_status=0
node "$here/a5-vm.mjs" || a5_status=$?
echo
echo "== live fixtures"
live_status=0
node "$here/drive.mjs" || live_status=$?
echo
echo "== exit: A5 $a5_status, live $live_status"
[ "$a5_status" -eq 0 ] && [ "$live_status" -eq 0 ]
