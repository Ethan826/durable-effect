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
import { mutants } from "./checkermutants.ts";

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

/** Runs the fixtures in the scratch copy, reporting in TAP. */
const runFixtures = () => {
  const run = spawnSync(process.execPath, [
    "--test", "--test-reporter=tap",
    join(copy, "fixtures.check.ts"), join(copy, "floors.check.ts"),
  ], { encoding: "utf8", env: plainEnv });
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

test("the fixtures pass on an unbroken copy of the suite", () => {
  const run = runFixtures();
  assert.equal(run.code, 0, run.out);
});

for (const [name, file, text, instead, failing] of mutants) {
  test(`a checker without ${name} fails the fixtures`, () => {
    const run = runWithout(file, text, instead);
    assert.notEqual(run.code, 0, "the fixtures passed the broken checker");
    const named = new RegExp(`^not ok \\d+ - ${failing}`, "m");
    assert.ok(named.test(run.out), run.out);
  });
}
