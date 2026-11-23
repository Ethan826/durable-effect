import { Effect } from "effect";
import type { LogEntry } from "./host.ts";
import type { Handler } from "./lifecycle.ts";

// I6's independent marker. The harness wraps the handler in an outermost
// Effect.ensuring of its own, which notes the log's length when it runs.
// It runs after every finalizer of the handler, so a root exit logged
// before the note was reported before the root's finalizers completed.
// Nothing here reads what the adapter reports.

/** Where the note is kept. */
interface Marker {
  at?: number;
}

/** Notes the log's length in `marker` when it runs. */
const noteLength = (log: ReadonlyArray<LogEntry>, marker: Marker) =>
  Effect.sync(() => {
    marker.at = log.length;
  });

/**
 * The handler with an outermost finalizer that notes the log's length,
 * and a reader of that note: `undefined` until the finalizer has run.
 */
export const markFinalized = (
  log: ReadonlyArray<LogEntry>,
  handler: Handler,
) => {
  const marker: Marker = {};
  return {
    handler: Effect.ensuring(handler, noteLength(log, marker)),
    finalized: (): number | undefined => marker.at,
  };
};
