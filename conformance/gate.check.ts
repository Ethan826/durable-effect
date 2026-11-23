import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import {
  cpSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from "node:fs";
import { join } from "node:path";
import { after, test } from "node:test";
import { fileURLToPath } from "node:url";

// The checker mutants (gate-integrity): each test copies the suite to a
// scratch directory, breaks one comparison of a checker there, and runs
// fixtures.check.ts against the copy. The run must fail, on the fixture
// named, or the fixtures would not notice that checker going blind. The
// copy is outside the real files, so the suite itself is never changed.

const root = fileURLToPath(new URL("..", import.meta.url));
const scratch = mkdtempSync(join(root, ".mutant-"));
after(() => rmSync(scratch, { recursive: true, force: true }));

const copy = join(scratch, "conformance");
cpSync(join(root, "conformance"), copy, { recursive: true });
symlinkSync(join(root, "src"), join(scratch, "src"));

/** The environment without the marker that makes a child a subtest. */
const plainEnv = Object.fromEntries(
  Object.entries(process.env).filter(([name]) => name !== "NODE_TEST_CONTEXT"),
);

/** Runs the fixtures in the scratch copy. */
const runFixtures = () => {
  const run = spawnSync(process.execPath,
    ["--test", join(copy, "fixtures.check.ts")],
    { encoding: "utf8", env: plainEnv });
  return { code: run.status, out: run.stdout };
};

/** Breaks `file` in the copy by replacing `text` once, and runs. */
const runWithout = (file: string, text: string, instead: string) => {
  const path = join(copy, file);
  const source = readFileSync(path, "utf8");
  assert.equal(source.split(text).length, 2, `${text} is not in ${file} once`);
  writeFileSync(path, source.replace(text, () => instead));
  const run = runFixtures();
  writeFileSync(path, source);
  return run;
};

/** A comparison, the checker it lives in, what turns it off, and what fails. */
const mutants: ReadonlyArray<readonly [string, string, string, string,
  string]> = [
  ["I1 and I2: logs compared", "properties.ts",
    "left.logHash === right.logHash && left.furtherHash === right.furtherHash",
    "true", "I1 catches a differing log"],
  ["I2: the paced run compared", "properties.ts",
    'I2: ["fresh2", "fresh0", "after"]', 'I2: ["fresh0", "after"]',
    "I2 catches a paced run whose log differs"],
  ["I7: a repeated id", "properties.ts",
    "new Set(run.identities).size !== run.identities.length", "false",
    "I7 catches a repeated id"],
  ["I7: ids between runs", "properties.ts",
    "JSON.stringify(left.identities) === JSON.stringify(right.identities)",
    "true", "I7 catches a repeated id"],
  ["I9: the limits", "properties.ts", "run[measure] > limit", "false",
    "I9 catches a run past each of its limits"],
  ["a missing run", "properties.ts", 'cause: "run", roles: missing',
    'cause: "property", roles: missing',
    "a run missing from a program is a run finding"],
  ["programs compared", "properties.ts", "compared[property].every(",
    "compared[property].some(",
    "programs compared counts the programs with every run needed"],
  ["the required program", "plan.ts", "run.index === requiredProgram.index",
    "true", "the scan floor needs the full budget and the required program"],
];

test("the fixtures pass on an unbroken copy of the suite", () => {
  const run = runFixtures();
  assert.equal(run.code, 0, run.out);
});

for (const [name, file, text, instead, failing] of mutants) {
  test(`a checker without ${name} fails the fixtures`, () => {
    const run = runWithout(file, text, instead);
    assert.notEqual(run.code, 0, "the fixtures passed the broken checker");
    assert.ok(run.out.includes(`✖ ${failing}`), run.out);
  });
}
