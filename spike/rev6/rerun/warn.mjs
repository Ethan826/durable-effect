// Fixture R6 (issue #48, step 3, rule 1 mitigation "detect"): the
// executor warns a second time, naming the run, when an aborted run is
// still running once the service's inactivity timeout has passed, the
// point past which R1 found other deliveries stall.
//
// Run i ignores its signal and takes 10 s. It loses a race to a 1 s
// sleep and is aborted. Four probe sleeps, issued with everything else
// at the start, complete at 1.5, 2.5, 3.5 and 4.5 s; the handler awaits
// each in turn while keeping i in the race, which shows where the
// stall begins. The service's inactivity timeout is 3 s.
//
// Main: the warning is due one inactivity timeout after the last
// command the handler sent. Control: one inactivity timeout after the
// abort. Both also warn once after a 1 s grace period from the abort.
import { noteAttempt, event, tag, tick, pause, effect }
  from "../runs/lib.mjs";

const inactivityMs = 3_000;
const graceMs = 1_000;
const probes = [1500, 2500, 3500, 4500];

// i: ignores its signal; records its effect; takes 10 s.
const ignoring = (ctx) => tag("i")(ctx.run("i", async () => {
  effect(ctx, "i");
  event(ctx, "i-start");
  await pause(10_000);
  event(ctx, "i-settle", "ok");
  return "i-ok";
}));

const labelOf = (winner) => winner.split("!")[0];

// Races `member` beside the kept run until `member` wins.
const awaitKeeping = async (ctx, race, kept, label, member) => {
  const next = () => tick(ctx, label, race([...kept.values(), member]));
  let winner = await next();
  while (kept.has(labelOf(winner))) {
    kept.delete(labelOf(winner));
    winner = await next();
  }
};

// Arms both warnings for i; `settled` is checked when each fires.
const armWarnings = (ctx, settled, abortAt, dueAt) => {
  const warn = (label) => () => {
    if (!settled.has("i")) event(ctx, label, "i");
  };
  setTimeout(warn("WARN-grace"), graceMs);
  setTimeout(warn("WARN-inactivity"), Math.max(0, dueAt - abortAt));
};

// `fromSend` on: due from the last command sent (main). Off: from abort.
const warnTwice = (sdk, fromSend) => async (ctx) => {
  noteAttempt(ctx, fromSend ? "r6" : "r6FromAbort");
  const { race } = sdk.RestatePromise;
  const run = ignoring(ctx);
  const first = tag("s")(ctx.sleep(1000));
  const issued = probes.map((ms) => [`p${ms}`, tag(`p${ms}`)(ctx.sleep(ms))]);
  const lastSent = Date.now();
  event(ctx, "issued", probes.join(","));
  await tick(ctx, "first", race([run, first]));
  const abortAt = Date.now();
  event(ctx, "abort-point");
  const settled = new Set();
  const due = (fromSend ? lastSent : abortAt) + inactivityMs;
  armWarnings(ctx, settled, abortAt, due);
  const kept = new Map([["i", run]]);
  for (const [label, probe] of issued) {
    await awaitKeeping(ctx, race, kept, label, probe);
    if (!kept.has("i")) settled.add("i");
  }
  if (kept.has("i")) await tick(ctx, "close", race([run]));
  settled.add("i");
  return "done";
};

/** R6 handlers, keyed by handler name. */
export const warnHandlers = (sdk) => ({
  r6: warnTwice(sdk, true),
  r6FromAbort: warnTwice(sdk, false)
});

/** R6's service options: a 3 s inactivity timeout. */
export const warnOptions = {
  journalRetention: 3600_000, inactivityTimeout: inactivityMs
};
