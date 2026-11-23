import { expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import { Schema } from "effect";
import * as Interface from "../../src/adapter/Interface.ts";

const runtimeV = new URL(
  "../../verification/proofs/Executor/Runtime.v",
  import.meta.url,
);

/** The constructor names of one inductive type, read from Runtime.v. */
const coqConstructors = (type: string): ReadonlyArray<string> => {
  const source = readFileSync(runtimeV, "utf8");
  const start = source.indexOf(`Inductive ${type} :=`);
  const end = source.indexOf(".\n", start);
  const arms = source.slice(start, end).split(":=")[1] ?? "";
  return arms
    .split("|")
    .map((arm) => arm.trim().split(/\s+/)[0] ?? "")
    .filter((name) => name !== "");
};

/** The naming rule: drop Coq's grouping prefix, keep the rest. */
const tagFor = (prefix: string) => (name: string): string =>
  prefix !== "" && name.startsWith(prefix) ? name.slice(prefix.length) : name;

type Literal = { readonly literal: unknown };
type Tag = { readonly schema: Literal };
type Tagged = { readonly fields: { readonly _tag: Tag } };

const tagsOf = (members: ReadonlyArray<Tagged>): ReadonlyArray<string> =>
  members.map((member) => String(member.fields._tag.schema.literal)).sort();

const decodesBack = <A, I>(
  schema: Schema.Codec<A, I>,
  raw: unknown,
): unknown => {
  const decoded = Schema.decodeUnknownSync(schema)(raw);
  return Schema.encodeSync(schema)(decoded);
};

const valueOf = (tag: string, value: number) => ({ _tag: tag, value });

const taskValues: ReadonlyArray<unknown> = [
  { _tag: "StartRoot" },
  { _tag: "RunQueued", task: 3 },
  { _tag: "Deliver", fiber: 1, token: 2, outcome: valueOf("Value", 7) },
  { _tag: "Deliver", fiber: 1, token: 2, outcome: valueOf("Failure", 0) },
  { _tag: "DeliverCancel", fiber: 1, token: 2 },
  { _tag: "DeliverDefect", fiber: 1, token: 2 },
  { _tag: "RequestInterrupt", fiber: 1 },
];

const sleepOf = (duration: unknown) => ({
  _tag: "Start",
  fiber: 1,
  token: 2,
  op: { _tag: "Sleep", duration },
});

const eventValues: ReadonlyArray<unknown> = [
  { _tag: "Start", fiber: 1, token: 2, op: { _tag: "Run", kind: 4, args: 5 } },
  sleepOf({ _tag: "Millis", millis: -5 }),
  sleepOf({ _tag: "Forever" }),
  { _tag: "Release", fiber: 1, token: 2 },
  { _tag: "Queue", priority: 0, task: 9 },
  { _tag: "FiberExited", fiber: 1 },
  { _tag: "RootExit", exit: { _tag: "Success", value: 1 } },
  { _tag: "RootExit", exit: { _tag: "Failure", value: 1 } },
  { _tag: "RootExit", exit: { _tag: "Interrupted" } },
  { _tag: "RootExit", exit: { _tag: "Defect" } },
];

test("every Task case survives decode then encode", () => {
  for (const raw of taskValues) {
    expect(decodesBack(Interface.Task, raw)).toEqual(raw);
  }
});

test("every Event case survives decode then encode", () => {
  for (const raw of eventValues) {
    expect(decodesBack(Interface.Event, raw)).toEqual(raw);
  }
});

test("decoding rejects a negative fiber and an unknown tag", () => {
  const decode = Schema.decodeUnknownResult(Interface.Task);
  expect(decode({ _tag: "RequestInterrupt", fiber: -1 })._tag).toBe("Failure");
  expect(decode({ _tag: "Nope" })._tag).toBe("Failure");
});

const pairs = [
  ["Op", "O", Interface.Op.members],
  ["Outcome", "", Interface.Outcome.members],
  ["RootExit", "Exit", Interface.RootExit.members],
  ["Task", "", Interface.Task.members],
  ["Event", "Ev", Interface.Event.members],
] as const;

test("case names equal Runtime.v's constructors, prefix dropped", () => {
  for (const [type, prefix, members] of pairs) {
    const expected = coqConstructors(type).map(tagFor(prefix)).sort();
    expect(expected.length).toBeGreaterThan(0);
    expect(tagsOf(members)).toEqual(expected);
  }
});
