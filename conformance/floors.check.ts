import assert from "node:assert/strict";
import { test } from "node:test";
import { makeAdapter } from "../src/adapter/Runtime.ts";
import { inventoryGaps } from "./inventory.ts";
import { listingGaps } from "./listing.ts";
import { fullScanOf, runLifecycle, zeroScans } from "./lifeplan.ts";
import type { LifeOutcome } from "./lifeplan.ts";
import { programsPerSeed, seeds } from "./plan.ts";
import { isRequiredSequence, sequenceScanFull } from "./strays.ts";

// Fixtures for the scan floors of the lifecycle and sequence runs, the
// grammar inventory and the file lists (gate-integrity). gate.check.ts
// runs this file against checkers with one comparison turned off, and each
// must fail.

const every = seeds.length * programsPerSeed;

test("an empty inventory, or a kind never generated, is a gap", () => {
  assert.deepEqual(inventoryGaps([], new Set(["Run"])),
    ["the grammar inventory is empty"]);
  assert.deepEqual(inventoryGaps(["Run", "Sleep"], new Set(["Run"])),
    ["no Sleep"]);
  assert.deepEqual(inventoryGaps(["Run"], new Set(["Run"])), []);
});

test("the lifecycle scan needs every program and the required one", () => {
  const all: LifeOutcome = {
    programs: every, violations: {}, scans: zeroScans, reachedRequired: true,
  };
  assert.equal(fullScanOf(all), true);
  assert.equal(fullScanOf({ ...all, reachedRequired: false }), false);
  assert.equal(fullScanOf({ ...all, programs: every - 1 }), false);
});

test("a lifecycle run reaches the required program only by its seed",
  async () => {
    const last = await runLifecycle(makeAdapter, 999, 1000);
    assert.equal(last.reachedRequired, true);
    const first = await runLifecycle(makeAdapter, 0, 1);
    assert.equal(first.reachedRequired, false);
  });

test("the required sequence is the 5,000th, of seed 5", () => {
  assert.equal(isRequiredSequence(5, 5000), true);
  assert.equal(isRequiredSequence(4, 5000), false);
  assert.equal(isRequiredSequence(5, 4999), false);
});

test("the sequence scan needs the exact count and the required one", () => {
  assert.equal(sequenceScanFull(every, true, every), true);
  assert.equal(sequenceScanFull(every, false, every), false);
  assert.equal(sequenceScanFull(every - 1, true, every), false);
  assert.equal(sequenceScanFull(every + 1, true, every), false);
});

const files = ["a.check.ts", "b.check.ts", "determinism.check.ts"];
const quick = ["a.check.ts", "b.check.ts"];

test("the file lists agree with the directory, in both directions", () => {
  assert.deepEqual(listingGaps(files, files, quick, 3), []);
  assert.deepEqual(listingGaps([...files, "c.check.ts"], files, quick, 3),
    ["c.check.ts is run by no script"]);
  assert.deepEqual(listingGaps(files, [...files, "c.check.ts"], quick, 3), [
    "c.check.ts is listed but not on disk",
    "c.check.ts is missing from the quick list",
  ]);
});

test("the quick list is the full list without determinism", () => {
  assert.deepEqual(listingGaps(files, files, ["a.check.ts"], 3),
    ["b.check.ts is missing from the quick list"]);
  assert.deepEqual(listingGaps(files, files, files, 3),
    ["determinism.check.ts should not be in the quick list"]);
  assert.deepEqual(listingGaps(files, files, [...quick, "x.check.ts"], 3),
    ["x.check.ts should not be in the quick list"]);
});

test("a directory below the minimum file count is a gap", () => {
  assert.deepEqual(listingGaps([], [], [], 3), ["only 0 files"]);
});
