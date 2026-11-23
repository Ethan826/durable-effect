import { expect, test } from "bun:test";
import { Effect } from "effect";
import type { AdapterRuntime, Host } from "../../src/adapter/Interface.ts";
import { makeAdapter } from "../../src/adapter/Runtime.ts";

/**
 * A host that counts registrations and, at the first one, sends StartRoot
 * again from inside the root's first slice.
 */
const reenteringHost = (
  registered: number[],
  adapter: () => AdapterRuntime,
): Host => ({
  emit: () => {},
  clock: () => 0,
  draw: () => 0,
  register: (fiber) => {
    registered.push(fiber);
    if (registered.length === 1) adapter().runTask({ _tag: "StartRoot" });
    return false;
  },
  inSlice: () => true,
  foreign: () => {},
});

test("a StartRoot sent during the root's first slice does nothing", () => {
  const registered: number[] = [];
  const adapter: AdapterRuntime = makeAdapter(
    Effect.succeed(1),
    0,
    reenteringHost(registered, () => adapter),
  );
  adapter.runTask({ _tag: "StartRoot" });
  expect(registered).toEqual([0]);
});
