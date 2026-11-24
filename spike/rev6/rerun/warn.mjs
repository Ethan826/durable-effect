// Fixture R6 (issue #48, step 3, rule 1 mitigation "detect"): the
// executor warns a second time, naming the run, when an aborted run is
// still running once the service's inactivity timeout has passed, the
// point past which R1 found other deliveries stall.
//
// Run i ignores its signal and takes 10 s. It loses a race to a 1 s
// sleep and is aborted. Five probe sleeps, issued with everything else
// at the start, complete at 1.5, 2.5, 3.5, 7 and 8 s; the handler
// awaits each in turn while keeping i in the race, which shows where
// the stall begins. The service's inactivity timeout is 3 s.
//
// Run 1 timed the warning from the last command sent and found no
// stall: deliveries 4.5 s after it arrived on time (run-out-1.txt). So
// a delivery also resets the server's clock. Main: the warning is due
// one inactivity timeout after the last exchange either way, a command
// sent or a result delivered. Control: after the last command sent
// (run 1's rule). Both also warn once 1 s after the abort.
import { noteAttempt, event, tag, tick, pause, effect }
  from "../runs/lib.mjs";

const inactivityMs = 3_000;
const graceMs = 1_000;
const probes = [1500, 2500, 3500, 7000, 8000];

// i: ignores its signal; records its effect; takes 10 s.
const ignoring = (ctx) => tag("i")(ctx.run("i", async () => {
  effect(ctx, "i");
  event(ctx, "i-start");
  await pause(10_000);
  event(ctx, "i-settle", "ok");
  return "i-ok";
}));

const labelOf = (winner) => winner.split("!")[0];

// The emulated executor's warning state for run i. `touch` records an
// exchange with the server and moves the inactivity warning to one
// timeout after it; the warning fires once, only after the abort, and
// only while i has not settled.
const warner = (ctx) => {
  const state = { aborted: false, settled: false, warned: false };
  let timer;
  const fire = () => {
    if (!state.aborted || state.settled || state.warned) return;
    state.warned = true;
    event(ctx, "WARN-inactivity", "i");
  };
  const touch = () => {
    clearTimeout(timer);
    timer = setTimeout(fire, inactivityMs);
  };
  const abort = () => {
    state.aborted = true;
    setTimeout(() => {
      if (!state.settled) event(ctx, "WARN-grace", "i");
    }, graceMs);
  };
  return { state, touch, abort };
};

// Races `member` beside the kept run until `member` wins; `onTick` is
// called after each delivery.
const awaitKeeping = async (ctx, race, kept, label, member, onTick) => {
  const next = async () => {
    const winner = await tick(ctx, label, race([...kept.values(), member]));
    onTick();
    return winner;
  };
  let winner = await next();
  while (kept.has(labelOf(winner))) {
    kept.delete(labelOf(winner));
    winner = await next();
  }
};

// `exchange` on: deliveries also move the warning (main). Off: only
// commands sent do (control, run 1's rule).
const warnTwice = (sdk, exchange) => async (ctx) => {
  noteAttempt(ctx, exchange ? "r6" : "r6FromSend");
  const { race } = sdk.RestatePromise;
  const w = warner(ctx);
  const onTick = exchange ? w.touch : () => {};
  const run = ignoring(ctx);
  const first = tag("s")(ctx.sleep(1000));
  const issued = probes.map((ms) => [`p${ms}`, tag(`p${ms}`)(ctx.sleep(ms))]);
  w.touch();
  event(ctx, "issued", probes.join(","));
  await tick(ctx, "first", race([run, first]));
  onTick();
  event(ctx, "abort-point");
  w.abort();
  const kept = new Map([["i", run]]);
  for (const [label, probe] of issued) {
    await awaitKeeping(ctx, race, kept, label, probe, onTick);
  }
  if (kept.has("i")) await tick(ctx, "close", race([run]));
  w.state.settled = true;
  return "done";
};

/** R6 handlers, keyed by handler name. */
export const warnHandlers = (sdk) => ({
  r6: warnTwice(sdk, true),
  r6FromSend: warnTwice(sdk, false)
});

/** R6's service options: a 3 s inactivity timeout. */
export const warnOptions = {
  journalRetention: 3600_000, inactivityTimeout: inactivityMs
};
