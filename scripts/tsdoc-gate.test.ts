import { afterAll, describe, expect, test } from "bun:test"
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import { join } from "node:path"

const gatePath = join(import.meta.dir, "vendor", "tsdoc-gate.ts")
const fixtures = join(import.meta.dir, "..", "fixtures", "tsdoc")

const runGate = (gate: string, args: ReadonlyArray<string>) => {
  const run = Bun.spawnSync(["bun", gate, ...args])
  return { code: run.exitCode, out: run.stdout.toString() }
}

describe("tsdoc gate", () => {
  test("an export with no TSDoc fails with exit 1 and names it", () => {
    const { code, out } = runGate(gatePath, [join(fixtures, "undocumented")])
    expect(code).toBe(1)
    expect(out).toContain("double: exported without TSDoc")
    expect(out).toContain("bare: exported without TSDoc")
    expect(out).not.toContain("ok: exported without TSDoc")
  })

  test("documented exports pass", () => {
    const { code, out } = runGate(gatePath, [join(fixtures, "documented")])
    expect(code).toBe(0)
    expect(out).toContain("tsdoc gate: OK (2 exported declarations")
  })

  test("a directory with no TypeScript files fails the inventory floor", () => {
    const { code, out } = runGate(gatePath, [join(fixtures, "empty")])
    expect(code).toBe(1)
    expect(out).toContain("no TypeScript files to check")
  })

  test("fewer exports than --min fails", () => {
    const documented = join(fixtures, "documented")
    const { code, out } = runGate(gatePath, ["--min", "3", documented])
    expect(code).toBe(1)
    expect(out).toContain("fewer than the minimum 3")
  })
})

// Fail closed: each of these is a finding, never a skip. The directory
// with the broken file also holds a documented one, so the parse is the
// only finding and the --min floor is not what fails it.
describe("tsdoc gate, fail closed", () => {
  test("a file that does not parse is a finding", () => {
    const { code, out } = runGate(gatePath, [join(fixtures, "syntax-error")])
    expect(code).toBe(1)
    expect(out).toContain("broken.ts:0: does not parse")
    expect(out).toContain("FAIL (1 findings")
  })

  test("an empty docblock is not TSDoc", () => {
    const { code, out } = runGate(gatePath, [join(fixtures, "empty-docblock")])
    expect(code).toBe(1)
    for (const name of ["spaces", "bare", "stars"]) {
      expect(out).toContain(`${name}: exported without TSDoc`)
    }
  })

  test("an export list naming nothing in the file is a finding", () => {
    const { code, out } = runGate(gatePath, [join(fixtures, "names-nothing")])
    expect(code).toBe(1)
    expect(out).toContain("export { a } names no declaration in this file")
  })
})

describe("checker mutant", () => {
  const scratch = mkdtempSync(join(import.meta.dir, ".mutant-"))
  afterAll(() => rmSync(scratch, { recursive: true, force: true }))

  const skipArrowExports = (source: string): string => {
    const target =
      "if (!ts.isExportAssignment(statement) && " +
      "!hasExportModifier(statement)) continue"
    const mutated = source.replace(
      target,
      `${target}\n    if (ts.isVariableStatement(statement)) continue`,
    )
    expect(mutated).not.toBe(source)
    return mutated
  }

  test(
    "a gate that skips variable (arrow) exports is caught by the fixture",
    () => {
      const mutant = join(scratch, "mutant-gate.ts")
      writeFileSync(mutant, skipArrowExports(readFileSync(gatePath, "utf8")))
      const arrowOnly = join(fixtures, "undocumented", "arrow.ts")
      const real = runGate(gatePath, [join(fixtures, "undocumented")])
      const mutated = runGate(mutant, [join(fixtures, "undocumented")])
      const expected = `${arrowOnly}:1: double: exported without TSDoc`
      expect(real.out).toContain(expected)
      expect(mutated.out).not.toContain("double: exported without TSDoc")
    },
  )
})
