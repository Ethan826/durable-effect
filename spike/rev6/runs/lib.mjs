// Helpers for the rev6-runs fixtures R1 to R4 (issue #48, step 3: the
// three executor rules for ctx.run and the abort signal). Handlers log
// what they saw, with wall-clock times; check.mjs decides. Wall time
// and timers here only shape logs and the emulated warning; they never
// change which durable commands a handler issues.
import { appendFileSync } from "node:fs";

const attempts = new Map();

/** The invocation id of the request a context serves. */
export const invocationOf = (ctx) => ctx.request().id;

/** Counts and logs one attempt of a handler; returns its number. */
export const noteAttempt = (ctx, name) => {
  const id = invocationOf(ctx);
  const n = (attempts.get(id) ?? 0) + 1;
  attempts.set(id, n);
  console.log("ATTEMPT", id, name, n, Date.now());
  return n;
};

/** The current attempt number of an invocation in this process. */
export const attemptOf = (ctx) => attempts.get(invocationOf(ctx)) ?? 0;

/** Logs one timed event: EV <id> <attempt> <label> <ms> <detail>. */
export const event = (ctx, label, detail = "") =>
  console.log("EV", invocationOf(ctx), attemptOf(ctx), label, Date.now(),
    detail);

/** Labels a promise's outcome so a race returns which member won. */
export const tag = (label) => (promise) =>
  promise.map((_value, failure) =>
    failure === undefined ? label : `${label}!${failure.code ?? "?"}`);

/** Awaits one race and logs its winner with the time it arrived. */
export const tick = async (ctx, label, combinator) => {
  const value = await combinator;
  event(ctx, `tick-${label}`, value);
  return value;
};

/** A non-durable wait, used only inside run closures. */
export const pause = (ms) =>
  new Promise((resolve) => setTimeout(resolve, ms));

const effectsFile = process.env.EFFECTS_FILE ?? "effects.log";

/** Records an external side effect outside the journal. */
export const effect = (ctx, key) =>
  appendFileSync(
    effectsFile,
    `EFFECT ${invocationOf(ctx)} ${key} ${attemptOf(ctx)} ${Date.now()}\n`);

/** Service options: a live variant and a forced-replay variant. */
export const retention = { journalRetention: 3600_000 };
export const replayOptions = { ...retention, inactivityTimeout: 200 };
