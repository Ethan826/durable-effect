import { expect, test } from "bun:test";
import { version } from "../src/index.ts";

test("the package exports its version", () => {
  expect(version).toBe("0.0.0");
});
