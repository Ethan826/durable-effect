// Helpers shared by the rev6-order and rev6-effects fixture handlers
// (register on #48). Handlers log what they saw; check.mjs decides.
// Wall time and timers here only shape turns and timestamps in the log;
// they never change which commands a handler issues.
import { appendFileSync } from "node:fs";

const attempts = new Map();

/** The invocation id of the request a context serves. */
export const invocationOf = (ctx) => ctx.request().id;

/** Counts and logs one attempt of a handler; returns its number. */
export const noteAttempt = (ctx, name) => {
  const id = invocationOf(ctx);
  const n = (attempts.get(id) ?? 0) + 1;
  attempts.set(id, n);
  console.log("ATTEMPT", id, name, n);
  return n;
};

/** The current attempt number of an invocation in this process. */
export const attemptOf = (ctx) => attempts.get(invocationOf(ctx)) ?? 0;

/** Labels a promise's outcome so a race returns which member won. */
export const tag = (label) => (promise) =>
  promise.map((_value, failure) =>
    failure === undefined ? label : `${label}!${failure.code ?? "?"}`);

/** Awaits one combinator and logs its value, or the error it threw. */
export const tick = async (ctx, label, combinator) => {
  const where = `${invocationOf(ctx)} ${attemptOf(ctx)} ${label}`;
  try {
    const value = await combinator;
    console.log("TICK", where, JSON.stringify(value));
    return value;
  } catch (error) {
    console.log("TICK", where, "caught", error.constructor.name);
    throw error;
  }
};

/** A non-durable wait, used only inside runs and sliced turns. */
export const pause = (ms) =>
  new Promise((resolve) => setTimeout(resolve, ms));

const effectsFile = process.env.EFFECTS_FILE ?? "effects.log";

/** Records an external side effect outside the journal. */
export const effect = (ctx, key) =>
  appendFileSync(
    effectsFile,
    `EFFECT ${invocationOf(ctx)} ${key} ${attemptOf(ctx)} ${Date.now()}\n`);

/** A turn of `slices` non-durable 100 ms waits with no durable await. */
export const slicedTurn = async (slices) => {
  for (let i = 0; i < slices; i += 1) {
    await pause(100);
  }
};

/** Service options: a live variant and a forced-replay variant. */
export const retention = { journalRetention: 3600_000 };
export const replayOptions = { ...retention, inactivityTimeout: 200 };
