#!/bin/sh
# Downloads the pinned TLA+ tools (TLC) into verification/tla/.tools/ and checks its SHA-256.
# Pinned: v1.7.4 ("Xenophanes"), the latest stable release as of 2026-11-21.
set -eu
cd "$(dirname "$0")"
version=v1.7.4
sha256=936a262061c914694dfd669a543be24573c45d5aa0ff20a8b96b23d01e050e88
mkdir -p .tools
jar=.tools/tla2tools-$version.jar
[ -f "$jar" ] || curl -fsSL -o "$jar" "https://github.com/tlaplus/tlaplus/releases/download/$version/tla2tools.jar"
actual=$(shasum -a 256 "$jar" | cut -d' ' -f1)
if [ "$sha256" != PINNED_SHA256 ] && [ "$actual" != "$sha256" ]; then
  echo "fetch-tla2tools.sh: checksum mismatch for $jar: $actual" >&2; rm -f "$jar"; exit 1
fi
echo "$jar $actual"
