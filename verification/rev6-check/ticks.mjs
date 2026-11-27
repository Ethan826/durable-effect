// ticks.mjs: the one place the step 7 tier's tick rule is stated (issue
// #49). tier.mjs explores a program with no ticks when dropsTicks holds,
// and tick.check.mjs checks by verdicts exactly the programs it accepts.
// It imports nothing, so the tier and the check cannot drift apart.

// Every statement of a list, with those nested in a body or a finalizer.
const statementsOf = (stmts) => stmts.flatMap(withNested);
const withNested = (s) =>
  [s, ...statementsOf(s.body ?? []), ...statementsOf(s.finalizer ?? [])];

const bodyOf = (fiber) => statementsOf(fiber.body);
const kindOf = (stmt) => stmt.s;

/** The statement kinds of a program, across its fibers and nested
 * blocks. */
export const kinds = (program) =>
  new Set(program.fibers.flatMap(bodyOf).map(kindOf));

/** True when the tier explores the program with no ticks: no statement
 * is a run, and the program does not have both a sleep and a clock read.
 * Only R1's stall reads ticks, and it needs a run; but ticks also move
 * true time, and at 1 fiber, 3 statements, 1 operation a sleep, an await
 * and a clock read showed an S8.P5 failure only with ticks. */
export const dropsTicks = (program) => {
  const has = kinds(program);
  return !has.has("run") && !(has.has("sleep") && has.has("clock"));
};
