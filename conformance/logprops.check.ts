import assert from "node:assert/strict";
import { test } from "node:test";
import { Brand } from "effect";
import type {
  Event,
  FiberId,
  RootExit,
  Token,
} from "../src/adapter/Interface.ts";
import type { CoqEntry } from "./logprops.ts";
import { i4Breach, i6Breach, i7Breach, i8Breach } from "./logprops.ts";

// Fixtures for the Runtime.v log properties: a log that keeps each, and
// for each clause a log that breaks only it, so every check is shown able
// to fail (gate-integrity).

const fiber = Brand.nominal<FiberId>();
const token = Brand.nominal<Token>();

const event = (one: Event): CoqEntry => ({ _tag: "LEvent", event: one });
const register = (id: number): CoqEntry =>
  ({ _tag: "LRegister", fiber: id });
const clock = (id: number): CoqEntry => ({ _tag: "LClock", fiber: id });
const start = (id: number, tok: number) => event({
  _tag: "Start", fiber: fiber(id), token: token(tok),
  op: { _tag: "Run", kind: 0, args: 0 },
});
const release = (id: number, tok: number) =>
  event({ _tag: "Release", fiber: fiber(id), token: token(tok) });
const deliver = (id: number, tok: number): CoqEntry => ({
  _tag: "LTask",
  task: {
    _tag: "Deliver", fiber: fiber(id), token: token(tok),
    outcome: { _tag: "Value", value: 0 },
  },
});
const exited = (id: number) =>
  event({ _tag: "FiberExited", fiber: fiber(id) });
const success: RootExit = { _tag: "Success", value: 0 };
const rootExit = event({ _tag: "RootExit", exit: success });
const startRoot: CoqEntry = { _tag: "LTask", task: { _tag: "StartRoot" } };

/** A log that keeps all four: start, await, delivery, release, exits. */
const good: ReadonlyArray<CoqEntry> = [
  startRoot, register(0), clock(0), start(0, 0), deliver(0, 0), clock(0),
  register(1), start(1, 1), release(1, 1), exited(1), exited(0), rootExit,
];

test("a log that keeps I4, I6, I7 and I8 passes each check", () => {
  const checks = [i4Breach, i6Breach, i7Breach, i8Breach];
  assert.deepEqual(checks.map((check) => check(good)),
    [undefined, undefined, undefined, undefined]);
});

test("I4: a fiber acting before its await ends is caught", () => {
  const log = [startRoot, register(0), start(0, 0), clock(0), deliver(0, 0)];
  assert.match(i4Breach(log) ?? "", /acts at entry 3/);
});

test("I4: an await still open keeps its fiber quiet to the end", () => {
  const log = [startRoot, register(0), start(0, 0), exited(0)];
  assert.match(i4Breach(log) ?? "", /before its await of token 0 ends/);
});

test("I4: a delivery to another fiber does not end the await", () => {
  const log = [register(0), start(0, 0), deliver(1, 0), clock(0)];
  assert.match(i4Breach(log) ?? "", /acts at entry 3/);
});

/** A task that ends fiber `id`'s await of `tok` without a value. */
const ending = (tag: "DeliverCancel" | "DeliverDefect") =>
  (id: number, tok: number): CoqEntry => ({
    _tag: "LTask",
    task: { _tag: tag, fiber: fiber(id), token: token(tok) },
  });

for (const tag of ["DeliverCancel", "DeliverDefect"] as const) {
  test(`I4: ${tag} ends an await, so the fiber may act after it`, () => {
    const log = [register(0), start(0, 0), ending(tag)(0, 0), clock(0)];
    assert.equal(i4Breach(log), undefined);
  });
}

test("I4: a token started twice is caught", () => {
  const log = [register(0), start(0, 0), deliver(0, 0), start(0, 0)];
  assert.match(i4Breach(log) ?? "", /token 0 started twice/);
});

test("I6: two root exits are caught", () => {
  assert.match(i6Breach([...good, rootExit]) ?? "", /2 root exits/);
});

test("I6: a root exit before the root's own exit is caught", () => {
  const log = [startRoot, register(0), rootExit, exited(0)];
  assert.match(i6Breach(log) ?? "", /before fiber 0 exited/);
});

test("I6: a root exit before any registration is caught", () => {
  assert.match(i6Breach([startRoot, rootExit]) ?? "", /before any fiber/);
});

test("I6: only the first fiber registered counts as the root", () => {
  const log = [register(0), register(1), exited(1), rootExit];
  assert.match(i6Breach(log) ?? "", /before fiber 0 exited/);
});

test("I7: a fiber registered twice is caught", () => {
  const log = [register(0), exited(0), register(0)];
  assert.match(i7Breach(log) ?? "", /fiber 0 registered twice/);
});

test("I8: an entry about a fiber before its registration is caught", () => {
  assert.match(i8Breach([clock(2), register(2)]) ?? "", /fiber 2 unborn/);
});

test("I8: an entry about a fiber after its exit is caught", () => {
  const log = [register(0), exited(0), clock(0)];
  assert.match(i8Breach(log) ?? "", /fiber 0 after its exit/);
});

test("I8: a second exit report is an entry after the exit", () => {
  const log = [register(0), exited(0), exited(0)];
  assert.match(i8Breach(log) ?? "", /after its exit/);
});
