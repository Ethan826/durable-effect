// Style gate: the counted rules of the house TypeScript style, decided on the
// syntax tree. Usage: bun scripts/style-gate.ts PATH... (files, or directories
// holding *.ts and *.tsx outside node_modules). Exit 1 with one line per
// breach, `file:line rule: detail`. Fails closed: no files, a missing path or
// a file that does not parse is a breach. Parsing uses `typescript-ast`, an
// alias of typescript 6.0.3 (TypeScript 7 has no classic compiler API).
//
// A declaration is a function-like node (signatures too) or a top-level
// `const` holding no function. A nested function is its own declaration.
// - depth (3): blocks nested in the declaration (body = 0); not braceless.
// - branches (8): `if`, each `case` (not `default`), `?:`, `&&`, `||`, `??`,
//   `catch`, wherever they appear. Cannot see `&&=`-style forms or `?.`.
// - bindings (8): names bound by `const`/`let`/`var` and parameters, the
//   declaration's own parameters included, destructured names counted singly.
// - lines (30): first to last line, from the `const` for a `const` arrow.
// - module-lines (250), columns (80): lines per file; UTF-16 units per line.
// - arrow-function: any non-generator `function` declaration or expression.
// - suppression: a comment naming a lint or type-check suppression marker
//   (the eslint disable forms, ts-ignore, ts-expect-error, ts-nocheck), found
//   by comment token, so a string is not one. Cannot see config or flags.
import { existsSync, readdirSync, readFileSync, statSync } from "node:fs"
import { join } from "node:path"
import ts from "typescript-ast"

/** One rule breach, printed as `file:line rule: detail`. */
export type Breach = Readonly<{
  file: string
  line: number
  rule: string
  detail: string
}>

const maxDepth = 3
const maxBranches = 8
const maxLines = 30
const maxBindings = 8
const maxModuleLines = 250
const maxColumns = 80
const suppression = /eslint-disable|@ts-ignore|@ts-expect-error|@ts-nocheck/
type Measure = Readonly<Record<"depth" | "branches" | "bindings", number>>

const none: Measure = { depth: 0, branches: 0, bindings: 0 }
const combine = (a: Measure, b: Measure): Measure => ({
  depth: Math.max(a.depth, b.depth),
  branches: a.branches + b.branches,
  bindings: a.bindings + b.bindings,
})

const breach = (file: string, line: number, rule: string, detail: string) =>
  ({ file, line, rule, detail }) satisfies Breach

const childrenOf = (node: ts.Node): ReadonlyArray<ts.Node> => {
  const found: ts.Node[] = []
  ts.forEachChild(node, (child) => {
    found.push(child)
  })
  return found
}

const nodesIn = (node: ts.Node): ReadonlyArray<ts.Node> =>
  [node, ...childrenOf(node).flatMap(nodesIn)]

const isUnit = ts.isFunctionLike
const notUnit = (node: ts.Node) => !isUnit(node)
const isBlockLike = (node: ts.Node): boolean =>
  ts.isBlock(node) || ts.isCaseBlock(node) || ts.isModuleBlock(node)

const logical: ReadonlySet<ts.SyntaxKind> = new Set([
  ts.SyntaxKind.AmpersandAmpersandToken,
  ts.SyntaxKind.BarBarToken,
  ts.SyntaxKind.QuestionQuestionToken,
])

const isBranch = (node: ts.Node): boolean =>
  ts.isIfStatement(node) ||
  ts.isCaseClause(node) ||
  ts.isConditionalExpression(node) ||
  ts.isCatchClause(node) ||
  (ts.isBinaryExpression(node) && logical.has(node.operatorToken.kind))

const namesIn = (name: ts.BindingName): number => {
  if (ts.isIdentifier(name)) return 1
  const elements: ReadonlyArray<ts.Node> = name.elements
  return elements
    .filter(ts.isBindingElement)
    .reduce((sum, element) => sum + namesIn(element.name), 0)
}

const bindingsAt = (node: ts.Node): number =>
  ts.isVariableDeclaration(node) || ts.isParameter(node)
    ? namesIn(node.name)
    : 0

const measure = (node: ts.Node, depth: number): Measure => {
  const here = isBlockLike(node) ? depth + 1 : depth
  const self = {
    depth: here,
    branches: isBranch(node) ? 1 : 0,
    bindings: bindingsAt(node),
  }
  const inside = (child: ts.Node) => measure(child, here)
  return childrenOf(node).filter(notUnit).map(inside).reduce(combine, self)
}

const measureKids = (node: ts.Node, step: (n: ts.Node) => Measure) =>
  childrenOf(node).filter(notUnit).map(step).reduce(combine, none)

const measureBody = (node: ts.Node): Measure =>
  ts.isBlock(node)
    ? measureKids(node, (kid) => measure(kid, 0))
    : measure(node, 0)

const measureUnit = (unit: ts.Node): Measure =>
  isUnit(unit) ? measureKids(unit, measureBody) : measure(unit, 0)

const holdsData = (node: ts.Node): boolean =>
  ts.isVariableStatement(node) &&
  node.declarationList.declarations.every(
    (d) => d.initializer === undefined || notUnit(d.initializer),
  )

const unitsIn = (file: ts.SourceFile): ReadonlyArray<ts.Node> => [
  ...nodesIn(file).filter(isUnit),
  ...file.statements.filter(holdsData),
]

// A `const f = () => {}` is measured from its `const`, not from the arrow.
const spanOf = (unit: ts.Node): ts.Node =>
  ts.isVariableDeclaration(unit.parent) &&
  ts.isVariableStatement(unit.parent.parent.parent)
    ? unit.parent.parent.parent
    : unit

const lineOf = (file: ts.SourceFile, position: number): number =>
  file.getLineAndCharacterOfPosition(position).line + 1

const checkUnit = (file: ts.SourceFile, path: string, unit: ts.Node) => {
  const span = spanOf(unit)
  const line = lineOf(file, span.getStart(file))
  const lines = lineOf(file, span.getEnd()) - line + 1
  const found = measureUnit(unit)
  const over = (rule: string, value: number, limit: number) =>
    value > limit ? [breach(path, line, rule, `${value}, limit ${limit}`)] : []
  return [
    ...over("depth", found.depth, maxDepth),
    ...over("branches", found.branches, maxBranches),
    ...over("bindings", found.bindings, maxBindings),
    ...over("lines", lines, maxLines),
  ]
}

const textBreaches = (path: string, text: string): ReadonlyArray<Breach> => {
  const lines = text.split(/\r?\n/)
  const count = text.endsWith("\n") ? lines.length - 1 : lines.length
  const wide = lines.flatMap((line, index) =>
    line.length > maxColumns
      ? [breach(path, index + 1, "columns", `${line.length}`)]
      : [],
  )
  return count > maxModuleLines
    ? [breach(path, 1, "module-lines", `${count}`), ...wide]
    : wide
}

const isPlain = (node: ts.Node): boolean =>
  (ts.isFunctionDeclaration(node) || ts.isFunctionExpression(node)) &&
  node.asteriskToken === undefined

const arrowBreaches = (file: ts.SourceFile, path: string) =>
  nodesIn(file)
    .filter(isPlain)
    .map((n) =>
      breach(path, lineOf(file, n.getStart(file)), "arrow-function", "use =>"),
    )

const isJsDoc = (node: ts.Node): boolean =>
  node.kind >= ts.SyntaxKind.FirstJSDocNode &&
  node.kind <= ts.SyntaxKind.LastJSDocNode

const tokensIn = (node: ts.Node, file: ts.SourceFile): ts.Node[] => {
  const kids = node.getChildren(file).filter((kid) => !isJsDoc(kid))
  return kids.length === 0 ? [node] : kids.flatMap((k) => tokensIn(k, file))
}

// Every comment is leading trivia of some token, the end-of-file token last.
const commentsIn = (file: ts.SourceFile): ReadonlyArray<ts.CommentRange> => {
  const ranges = tokensIn(file, file).flatMap(
    (token) => ts.getLeadingCommentRanges(file.text, token.pos) ?? [],
  )
  return [...new Map(ranges.map((range) => [range.pos, range])).values()]
}

const suppressionBreaches = (file: ts.SourceFile, path: string) =>
  commentsIn(file)
    .filter((r) => suppression.test(file.text.slice(r.pos, r.end)))
    .map((r) => breach(path, lineOf(file, r.pos), "suppression", "directive"))

const parses = (path: string, text: string): boolean =>
  ts.transpileModule(text, { fileName: path, reportDiagnostics: true })
    .diagnostics?.length === 0

/** Every breach of the style rules in one file's `text`. */
export const checkSource = (path: string, text: string) => {
  if (!parses(path, text))
    return [breach(path, 0, "parse", "does not parse; cannot be checked")]
  const file = ts.createSourceFile(path, text, ts.ScriptTarget.Latest, true)
  return [
    ...textBreaches(path, text),
    ...unitsIn(file).flatMap((unit) => checkUnit(file, path, unit)),
    ...arrowBreaches(file, path),
    ...suppressionBreaches(file, path),
  ]
}

const sourcesUnder = (path: string): ReadonlyArray<string> => {
  if (!statSync(path).isDirectory()) return [path]
  return readdirSync(path).flatMap((entry) => {
    const child = join(path, entry)
    if (statSync(child).isDirectory())
      return entry === "node_modules" ? [] : sourcesUnder(child)
    return /\.tsx?$/.test(entry) && !entry.endsWith(".d.ts") ? [child] : []
  })
}

/**
 * Checks every file named in `paths` or under a named directory. A missing
 * path, no files at all and an unparsable file are each a breach.
 */
export const checkPaths = (paths: ReadonlyArray<string>) => {
  const missing = paths.filter((path) => !existsSync(path))
  const files = paths.filter(existsSync).flatMap(sourcesUnder)
  const empty = files.length === 0 ? paths.join(" ") : undefined
  const noFiles = breach(empty ?? "", 0, "inventory", "no TypeScript files")
  return {
    files: files.length,
    breaches: [
      ...missing.map((p) => breach(p, 0, "missing", "no such path")),
      ...(empty === undefined ? [] : [noFiles]),
      ...files.flatMap((p) => checkSource(p, readFileSync(p, "utf8"))),
    ],
  }
}

if (import.meta.main) {
  const { breaches, files } = checkPaths(process.argv.slice(2))
  for (const b of breaches)
    console.log(`${b.file}:${b.line} ${b.rule}: ${b.detail}`)
  if (breaches.length === 0) console.log(`style gate: OK (${files} files)`)
  process.exit(breaches.length === 0 ? 0 : 1)
}
