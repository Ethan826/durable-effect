# Gaps on #46, sourced by run.sh after the deployment is registered: the per-tick race with dropped
# calls and awakeables, dropped operations that complete meanwhile, cancellation with a dropped
# operation pending, and several operations awaited together. Uses $state and the ports of run.sh.
gmark=$(wc -l < "$state/sdk.log")
smark=$(wc -l < "$state/server.log")
ingress=http://127.0.0.1:19891
gq() {
  jq -n --arg q "$1" '{query: $q}' \
    | curl -sS -H 'Content-Type: application/json' -H 'Accept: application/json' -d @- http://127.0.0.1:19890/query \
    | jq -c '.rows[]'
}
gjournal() {
  echo "  journal of $1:"
  gq "SELECT index, entry_type, name, completed, invoked_id, invoked_target, entry_lite_json FROM sys_journal WHERE id = '$1' ORDER BY index" | sed 's/^/    /'
}
gstatus() {
  gq "SELECT id, target, status, retry_count, completion_result, completion_failure, last_failure FROM sys_invocation WHERE id = '$1'" | sed 's/^/  /'
}
gchildren() {
  echo "  child invocations:"
  gq "SELECT id, target, status, retry_count, completion_result, completion_failure FROM sys_invocation WHERE invoked_by_id = '$1'" | sed 's/^/    /'
}
# Calls a handler request-response, prints its result, and leaves its invocation id in $inv.
gcall() {
  printf '%s result ' "$1"
  curl -sS --max-time 60 -D "$state/gheaders" -H 'Content-Type: application/json' -d 'null' "$ingress/$1"; echo
  inv=$(grep -i '^x-restate-id:' "$state/gheaders" | awk '{print $2}' | tr -d '\r')
}
echo
echo "== Gaps on #46: per-tick race with calls, awakeables, cancellation and all =="
for svc in Gap GapReplay; do
  echo
  echo "-- $svc/dropCall"
  gcall "$svc/dropCall"; gstatus "$inv"; gjournal "$inv"; gchildren "$inv"
  sleep 4
  echo " 4 s later, after the child's 3 s sleep:"
  gstatus "$inv"; gjournal "$inv"; gchildren "$inv"

  echo
  echo "-- $svc/dropAwakeable"
  gcall "$svc/dropAwakeable"; gstatus "$inv"; gjournal "$inv"

  echo
  echo "-- $svc/dropAwakeableResolvedLater"
  (gcall "$svc/dropAwakeableResolvedLater"; echo "$inv" > "$state/ginv") > "$state/gout" 2>&1 & call_pid=$!
  sleep 2.5
  awk_id=$(grep "AWAKEABLE $svc/dropAwakeableResolvedLater" "$state/sdk.log" | tail -1 | awk '{print $NF}')
  echo " resolving $awk_id from outside during race2"
  curl -sS -o /dev/null -w ' resolve request HTTP %{http_code}\n' -H 'Content-Type: application/json' -d '"outside"' "$ingress/restate/awakeables/$awk_id/resolve"
  wait "$call_pid"
  cat "$state/gout"; inv=$(cat "$state/ginv"); gstatus "$inv"; gjournal "$inv"

  echo
  echo "-- $svc/dropCompletesMeanwhile"
  gcall "$svc/dropCompletesMeanwhile"; gstatus "$inv"; gjournal "$inv"

  echo
  echo "-- $svc/dropCallCompletesMeanwhile"
  gcall "$svc/dropCallCompletesMeanwhile"; gstatus "$inv"; gjournal "$inv"; gchildren "$inv"

  echo
  echo "-- $svc/cancelWithDropped"
  inv=$(curl -sS -H 'Content-Type: application/json' -d 'null' "$ingress/$svc/cancelWithDropped/send" | jq -r .invocationId)
  echo "$svc/cancelWithDropped invocation $inv"
  sleep 3
  echo " before cancel:"; gstatus "$inv"; gjournal "$inv"
  curl -sS -X PATCH -o /dev/null -w ' cancel request HTTP %{http_code}\n' "http://127.0.0.1:19890/invocations/$inv/cancel"
  sleep 3
  echo " after cancel:"; gstatus "$inv"; gjournal "$inv"

  echo
  echo "-- $svc/allOfTwo"
  gcall "$svc/allOfTwo"; gstatus "$inv"; gjournal "$inv"
done
sleep 2
echo
echo "== SDK log for the gaps =="
tail -n +"$((gmark + 1))" "$state/sdk.log" | grep -E "ATTEMPT|TICK|AWAKEABLE|WARN|Error|Replaying|uspend|ancel" | sed -E 's/\[restate\]\[[^]]*\]//; s/\[inv_[^]]*\]//'
echo
echo "== SDK log WARN count for the gaps: $(tail -n +"$((gmark + 1))" "$state/sdk.log" | grep -c WARN || true)"
echo "== Server log WARN and ERROR lines for the gaps =="
tail -n +"$((smark + 1))" "$state/server.log" | grep -E "WARN|ERROR" || echo "  (none)"
