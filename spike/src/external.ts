// A fake external service whose state lives on disk, so it survives a crash of the endpoint.
import { existsSync, readFileSync, rmSync, writeFileSync } from "node:fs"

const file = new URL("../data/external.json", import.meta.url)
interface Store { calls: Record<string, number>; applied: Record<string, number> }

const load = (): Store => existsSync(file) ? JSON.parse(readFileSync(file, "utf8")) : { calls: {}, applied: {} }
const save = (store: Store) => writeFileSync(file, JSON.stringify(store, null, 2))

/** Counts a call for `key` and returns its 1-based attempt number. */
export const attemptCall = (key: string): number => {
  const store = load()
  store.calls[key] = (store.calls[key] ?? 0) + 1
  save(store)
  return store.calls[key]
}

/** An idempotent write: every call is counted, but a key is applied once. */
export const externalWrite = (idempotencyKey: string) => {
  const store = load()
  store.calls[idempotencyKey] = (store.calls[idempotencyKey] ?? 0) + 1
  store.applied[idempotencyKey] = 1
  save(store)
  return { calls: store.calls[idempotencyKey], applied: Object.keys(store.applied).filter(k => k === idempotencyKey).length }
}

/** Kills the process once, after the write and before Restate persists the step, if armed for `key`. */
export const crashIfArmed = (key: string) => {
  const flag = new URL(`../data/crash-${key}`, import.meta.url)
  if (existsSync(flag)) {
    rmSync(flag)
    process.exit(1)
  }
}
