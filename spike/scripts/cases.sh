#!/bin/sh
# Invokes Spike/<handler> with <json> through ingress, then prints the journal check for it.
cd "$(dirname "$0")/.."
handler=$1; body=$2
out=$(curl -s -m 60 -D - "localhost:8080/Spike/$handler" -H 'content-type: application/json' -d "$body")
id=$(printf '%s' "$out" | tr -d '\r' | awk 'tolower($1)=="x-restate-id:"{print $2}')
echo "=== $handler $body"
printf '%s\n' "$out" | tail -1; echo
node scripts/inspect.mjs "$id"
