import assert from "node:assert/strict";
import { readdirSync, readFileSync } from "node:fs";
import { test } from "node:test";
import { fileURLToPath } from "node:url";
import { listingGaps } from "./listing.ts";

// The scripts in package.json name every conformance file by hand, so that
// bare `bun test` and a glob never pick them up by accident. A file that no
// script names would run nowhere. This compares the lists with the
// directory (fixtures for the comparison are in floors.check.ts).

/** The fewest check files the directory has: 14 when this was written. */
const minimumFiles = 14;

const root = fileURLToPath(new URL("..", import.meta.url));

const scripts: Record<string, string> =
  JSON.parse(readFileSync(`${root}package.json`, "utf8")).scripts;

/** The conformance files a script runs, as bare names. */
const filesOf = (name: string): ReadonlyArray<string> =>
  (scripts[name] ?? "").split(" ").filter((word) =>
    word.startsWith("conformance/")
  ).map((word) => word.slice("conformance/".length));

const onDisk = readdirSync(`${root}conformance`).filter((name) =>
  name.endsWith(".check.ts")
);

test("every conformance check file is in the scripts, and the other way",
  () => {
    const full = filesOf("conformance");
    assert.ok(full.length >= minimumFiles, `${full.length} listed`);
    assert.deepEqual(
      listingGaps(onDisk, full, filesOf("conformance:quick"), minimumFiles),
      [],
    );
  });
