import { afterAll, describe, expect, test } from "bun:test"
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs"
import { join } from "node:path"

const gatePath = join(import.meta.dir, "style-gate.ts")
const fixtures = join(import.meta.dir, "fixtures", "style")
const scratch = mkdtempSync(join(import.meta.dir, ".mutant-"))
afterAll(() => rmSync(scratch, { recursive: true, force: true }))

const runGate = (gate: string, args: ReadonlyArray<string>) => {
  const run = Bun.spawnSync(["bun", gate, ...args])
  return { code: run.exitCode, out: run.stdout.toString() }
}

const breachesIn = (out: string): ReadonlyArray<string> =>
  out.split("\n").filter((line) => /:\d+ [a-z-]+:/.test(line))

const mutantOf = (name: string, pattern: RegExp, text: string): string => {
  const source = readFileSync(gatePath, "utf8")
  const mutated = source.replace(pattern, text)
  expect(mutated).not.toBe(source)
  const path = join(scratch, `${name}.ts`)
  writeFileSync(path, mutated)
  return path
}

const mustFail: ReadonlyArray<readonly [string, string, number]> = [
  ["depth", "depth.ts", 1],
  ["branches", "nine.ts", 1],
  ["branches", "mixed.ts", 1],
  ["lines", "long.ts", 1],
  ["bindings", "nine.ts", 1],
  ["module-lines", "long.ts", 1],
  ["columns", "wide.ts", 2],
  ["arrow-function", "declaration.ts", 1],
]

describe("each rule fails on its own fixture and on no other rule", () => {
  for (const [rule, file, line] of mustFail) {
    test(`${rule}/${file}`, () => {
      const target = join(fixtures, rule, file)
      const { code, out } = runGate(gatePath, [target])
      expect(code).toBe(1)
      expect(breachesIn(out)).toHaveLength(1)
      expect(out).toContain(`${target}:${line} ${rule}:`)
    })
  }
})

describe("suppression comments", () => {
  test("every directive is reported by its line", () => {
    const { code, out } = runGate(gatePath, [join(fixtures, "suppression")])
    const found = breachesIn(out)
    expect(code).toBe(1)
    expect(found.every((line) => line.includes(" suppression:"))).toBe(true)
    expect(found.map((line) => line.split(" ")[0]?.split(":").pop())).toEqual(
      ["1", "2", "3", "4"],
    )
  })
})

describe("passing input", () => {
  test("files at every limit, with directive text in strings, pass", () => {
    const { code, out } = runGate(gatePath, [join(fixtures, "pass")])
    expect(code).toBe(0)
    expect(out).toContain("style gate: OK (2 files)")
  })
})

describe("failing closed", () => {
  test("a directory with no TypeScript files fails the floor", () => {
    const { code, out } = runGate(gatePath, [join(fixtures, "empty")])
    expect(code).toBe(1)
    expect(out).toContain("no TypeScript files")
  })

  test("a file that does not parse fails instead of being skipped", () => {
    const broken = join(scratch, "broken.ts")
    writeFileSync(broken, "export const = ;\n")
    const { code, out } = runGate(gatePath, [broken])
    expect(code).toBe(1)
    expect(out).toContain("broken.ts:0 parse:")
  })

  test("a missing path and no arguments fail", () => {
    expect(runGate(gatePath, [join(fixtures, "absent")]).code).toBe(1)
    expect(runGate(gatePath, []).code).toBe(1)
  })
})

describe("a gate with one limit raised misses that rule's fixture", () => {
  const limits = [
    ["maxDepth", "depth"],
    ["maxBranches", "branches"],
    ["maxLines", "lines"],
    ["maxBindings", "bindings"],
    ["maxModuleLines", "module-lines"],
    ["maxColumns", "columns"],
  ] as const

  for (const [name, rule] of limits) {
    test(name, () => {
      const raised = new RegExp(`${name} = \\d+`)
      const mutant = mutantOf(name, raised, `${name} = 9999`)
      const target = join(fixtures, rule)
      expect(runGate(gatePath, [target]).code).toBe(1)
      expect(runGate(mutant, [target]).code).toBe(0)
    })
  }
})

describe("a gate that never matches a directive", () => {
  test("misses the suppression fixture", () => {
    const mutant = mutantOf("directive", /suppression\.test\(/, "false && $&")
    const target = join(fixtures, "suppression")
    expect(runGate(gatePath, [target]).code).toBe(1)
    expect(runGate(mutant, [target]).code).toBe(0)
  })
})
