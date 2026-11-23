import assert from "node:assert/strict";
import { test } from "node:test";
import { Brand, Effect } from "effect";
import type { TaskId } from "../src/adapter/Interface.ts";
import { makeAdapter } from "../src/adapter/Runtime.ts";
import { scriptedHost } from "./host.ts";
import type { LogEntry } from "./host.ts";

// The scripted host's side of #37 I3: the executor discards any task
// queued outside a slice of one of its turns. (host.test.ts is at the
// 250-line limit, so these tests live here.)

const journal = { outcomes: [], cancelBefore: undefined };
const taskId = Brand.nominal<TaskId>();

const sentRunQueued = (log: ReadonlyArray<LogEntry>) => log.flatMap((entry) =>
  entry._tag === "Sent" && entry.task._tag === "RunQueued"
    ? [entry.task.task]
    : []
);

test("a Queue outside a slice is logged as discarded and never run", () => {
  const host = scriptedHost(journal, { seed: 0 });
  host.emit({ _tag: "Queue", priority: 0, task: taskId(9) });
  host.run(makeAdapter(Effect.void, 0, host));
  assert.deepEqual(host.log[0], { _tag: "Discarded", task: 9 });
  assert.deepEqual(sentRunQueued(host.log), []);
});

test("a foreign resume is reported and its continuation never runs", () => {
  const host = scriptedHost(journal, { seed: 0 });
  const cell = { value: 0 };
  const out: { resume?: (effect: Effect.Effect<number>) => void } = {};
  const program = Effect.callback<number>((resume) => {
    out.resume = resume;
  }).pipe(Effect.flatMap((value) => Effect.sync(() => {
    cell.value = value;
  })));
  const adapter = makeAdapter(program, 0, host);
  host.run(adapter);
  out.resume?.(Effect.succeed(7));
  assert.equal(cell.value, 0);
  assert.deepEqual(host.log.slice(-2), [
    { _tag: "Foreign", kind: "resume", fiber: 0 },
    { _tag: "Discarded", task: 0 },
  ]);
});
