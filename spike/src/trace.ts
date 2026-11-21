// Appends what each handler attempt observes (clock reads, draws, sleeps) to a JSONL file, so the
// attempts of one invocation, including replays, can be compared. Spike instrumentation only.
import { appendFileSync, mkdirSync } from "node:fs"

const dir = new URL("../data/", import.meta.url)
mkdirSync(dir, { recursive: true })
const file = new URL("trace.jsonl", dir)

const attempts = new Map<string, number>()

export const record = (invocationId: string, event: { readonly kind: string } & Record<string, unknown>) => {
  if (event.kind === "attempt-start") attempts.set(invocationId, (attempts.get(invocationId) ?? 0) + 1)
  appendFileSync(file, JSON.stringify({ ...event, pid: process.pid, invocationId, attempt: attempts.get(invocationId) ?? 0 }) + "\n")
}
