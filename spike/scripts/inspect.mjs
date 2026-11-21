// Prints an invocation's journal and checks that every attempt's trace (clock reads, draws,
// sleeps, typed failures) is a prefix of the last attempt's. Usage: node scripts/inspect.mjs <invocationId>
import { readFileSync } from "node:fs"
const id = process.argv[2]
const res = await fetch("http://127.0.0.1:9070/query", {
  method: "POST", headers: { "content-type": "application/json", accept: "application/json" },
  body: JSON.stringify({ query: `SELECT index, entry_type, name, entry_json FROM sys_journal WHERE id = '${id}' ORDER BY index` })
})
const { rows } = await res.json()
console.log("journal:")
for (const r of rows) console.log(" ", r.index, r.entry_type, r.name ?? "", (r.entry_json ?? "").slice(0, 160))
const events = readFileSync(new URL("../data/trace.jsonl", import.meta.url), "utf8").trim().split("\n")
  .map(l => JSON.parse(l)).filter(e => e.invocationId === id)
const byAttempt = Map.groupBy(events, e => `${e.pid}:${e.attempt}`)
const strip = ({ pid, attempt, invocationId, ...rest }) => JSON.stringify(rest)
const seqs = [...byAttempt.values()].map(es => es.map(strip))
const last = seqs.at(-1)
const bad = seqs.filter(s => s.some((e, i) => e !== last[i]))
console.log(`attempts: ${seqs.length}; lengths: ${seqs.map(s => s.length).join(",")}; non-prefix attempts: ${bad.length}`)
console.log("final attempt trace:"); for (const e of last) console.log(" ", e)
