// Handlers for the rev6-idem fixtures (A39 to A42 of the assumptions register on #48).
// Every wait on a durable operation is one fresh RestatePromise.race, as in ../cancel.
//
// Log lines the driver reads (SDK log):
//   ATTEMPT <service>/<handler> <n> <invocation id>
//   EVENT <invocation id> <json>          a step's outcome
// Counter file (COUNTER_FILE, outside the journal), appended synchronously:
//   BODY <label> <invocation id> <attempt>   the target's handler body was entered
//   APPLY <label> <invocation id> <step>     a counted ctx.run action body executed
import { appendFileSync } from "node:fs";
import http2 from "node:http2";

const sdk = await import(`${process.env.SDK_DIR}/dist/index.js`);
const { RestatePromise, rpc } = sdk;
const { race } = RestatePromise;
const COUNTER_FILE = process.env.COUNTER_FILE;

const attempts = new Map();
const invocation = (ctx) => ctx.request().id;
const attemptOf = (ctx) => attempts.get(invocation(ctx)) ?? 0;
const begin = (ctx, handler) => {
  const id = invocation(ctx);
  const n = (attempts.get(id) ?? 0) + 1;
  attempts.set(id, n);
  console.log("ATTEMPT", `${ctx.request().target.service}/${handler}`, n, id);
};
const event = (ctx, body) => console.log("EVENT", invocation(ctx), JSON.stringify({ attempt: attemptOf(ctx), ...body, at: Date.now() }));
const count = (line) => appendFileSync(COUNTER_FILE, `${line}\n`);
const wait = (ms) => new Promise((resolve) => setTimeout(resolve, ms));
const counted = (ctx, label, step) => async () => {
  count(`APPLY ${label} ${invocation(ctx)} ${step}`);
  return step;
};
const errorOf = (e) => ({ error: e?.constructor?.name, code: e?.code, message: e?.message });
const settle = async (ctx, step, combinator) => {
  event(ctx, { step: `${step}:start` });
  const started = Date.now();
  try {
    const value = await combinator;
    const outcome = { step, settled: "resolved", value, ms: Date.now() - started };
    event(ctx, outcome);
    return outcome;
  } catch (e) {
    const outcome = { step, settled: "rejected", ...errorOf(e), ms: Date.now() - started };
    event(ctx, outcome);
    return outcome;
  }
};

// ---- the target: the compensation step whose idempotency key is under test ----
// arg: { label, busyMs, preSteps, holdMs, leafMs }
//   busyMs   plain (non-durable) wait before the first durable step
//   preSteps counted ctx.run steps before the hold
//   holdMs   durable sleep before the "apply" step
//   leafMs   if set, a call to IdLeaf/hold (a grandchild) awaited before "apply"
const applyBody = async (ctx, arg) => {
  begin(ctx, "apply");
  count(`BODY ${arg.label} ${invocation(ctx)} ${attemptOf(ctx)}`);
  event(ctx, { step: "body", label: arg.label });
  if (arg.busyMs) await wait(arg.busyMs);
  for (let i = 0; i < (arg.preSteps ?? 0); i++) await race([ctx.run(`pre${i}`, counted(ctx, arg.label, `pre${i}`))]);
  if (arg.holdMs) {
    event(ctx, { step: "hold:start", label: arg.label });
    await race([ctx.sleep(arg.holdMs)]);
  }
  if (arg.leafMs) {
    event(ctx, { step: "leaf:start", label: arg.label });
    await race([ctx.serviceClient(leaf).hold({ label: `${arg.label}-leaf`, ms: arg.leafMs })]);
  }
  await race([ctx.run("apply", counted(ctx, arg.label, "apply"))]);
  event(ctx, { step: "applied", label: arg.label });
  return `applied:${arg.label}`;
};
const leaf = sdk.service({
  name: "IdLeaf",
  handlers: {
    hold: async (ctx, arg) => {
      begin(ctx, "hold");
      count(`BODY ${arg.label} ${invocation(ctx)} ${attemptOf(ctx)}`);
      event(ctx, { step: "body", label: arg.label });
      await race([ctx.sleep(arg.ms)]);
      await race([ctx.run("apply", counted(ctx, arg.label, "apply"))]);
      return `held:${arg.label}`;
    }
  },
  options: { journalRetention: 3600_000 }
});
const target = sdk.service({ name: "IdTarget", handlers: { apply: applyBody }, options: { journalRetention: 3600_000 } });
// The same handler with a 4 s idempotency retention, to see what happens after it expires.
const short = sdk.service({ name: "IdShort", handlers: { apply: applyBody }, options: { idempotencyRetention: 4000, journalRetention: 4000 } });
// A virtual object: a call to a locked key waits in the inbox, which is case (a), "before start".
const object = sdk.object({
  name: "IdObject",
  handlers: {
    apply: applyBody,
    hold: async (ctx, ms) => {
      begin(ctx, "hold");
      event(ctx, { step: "hold:start" });
      await race([ctx.sleep(ms)]);
      return "released";
    }
  },
  options: { journalRetention: 3600_000 }
});

// ---- callers ----
// target: "IdTarget" | "IdShort" | "IdObject:<key>"
const callTarget = (ctx, targetName, arg, key) => {
  // The SDK rejects an explicit undefined second argument, so the options go in only with a key.
  const opts = key ? [rpc.opts({ idempotencyKey: key })] : [];
  if (targetName.startsWith("IdObject:")) return ctx.objectClient(object, targetName.slice("IdObject:".length)).apply(arg, ...opts);
  return ctx.serviceClient(targetName === "IdShort" ? short : target).apply(arg, ...opts);
};
const sleepFor = (ctx, ms) => race([ctx.sleep(ms).map(() => `slept${ms}`)]);

// G2: one call with an idempotency key from a handler.
const callWithKey = async (ctx, { target: t, key, arg }) => {
  begin(ctx, "callWithKey");
  return settle(ctx, "call", race([callTarget(ctx, t, arg, key)]));
};

// G3: the revision 6 scenario. A first cancel interrupts the main wait; compensation calls the
// target with key; a second cancel makes the SDK cancel that call (A7); after a durable gap the
// parent reissues with reissueKey, then once more after a second gap.
// variant "call" uses a request-response call; "sendAttach" sends with the key and attaches.
const compensate = async (ctx, { variant, target: t, key, reissueKey, arg, gapMs }) => {
  begin(ctx, "compensate");
  await settle(ctx, "x", race([ctx.sleep(60000).map(() => "sleep60s")]));
  event(ctx, { step: "comp-start" });
  if (variant === "sendAttach") return compensateAttach(ctx, key, arg, gapMs);
  const y = await settle(ctx, "y", race([callTarget(ctx, t, arg, key)]));
  await settle(ctx, "gap", sleepFor(ctx, gapMs));
  const re = await settle(ctx, "re", race([callTarget(ctx, t, arg, reissueKey)]));
  await settle(ctx, "gap2", sleepFor(ctx, gapMs));
  const re2 = await settle(ctx, "re2", race([callTarget(ctx, t, arg, reissueKey)]));
  return { y, re, re2 };
};
const compensateAttach = async (ctx, key, arg, gapMs) => {
  const handle = ctx.serviceSendClient(target).apply(arg, rpc.sendOpts({ idempotencyKey: key }));
  const childId = await handle.invocationId;
  event(ctx, { step: "sent", childId });
  const y = await settle(ctx, "y", race([ctx.attach(childId)]));
  await settle(ctx, "gap", sleepFor(ctx, gapMs));
  const re = await settle(ctx, "re", race([ctx.attach(childId)]));
  return { y, re };
};

// G4 (A40): a completed call, then a cancel, then compensation with a one-way send and a call
// whose target calls a grandchild; the driver kills (or, in the control, cancels again) the parent.
const killDuring = async (ctx, { prefix, key }) => {
  begin(ctx, "killDuring");
  await settle(ctx, "c0", race([callTarget(ctx, "IdTarget", { label: `${prefix}-c0` })]));
  await settle(ctx, "x", race([ctx.sleep(60000).map(() => "sleep60s")]));
  event(ctx, { step: "comp-start" });
  ctx.serviceSendClient(leaf).hold({ label: `${prefix}-send`, ms: 20000 });
  const y = await settle(ctx, "y", race([callTarget(ctx, "IdTarget", { label: `${prefix}-call`, preSteps: 1, leafMs: 20000 }, key)]));
  const after = await settle(ctx, "after", race([ctx.run("after", counted(ctx, `${prefix}-parent`, "after"))]));
  return { y, after };
};

// G6 (A42): two compensation calls in sequence; the driver sends a cancel during each.
const threeCancels = async (ctx, { prefix }) => {
  begin(ctx, "threeCancels");
  await settle(ctx, "x", race([ctx.sleep(60000).map(() => "sleep60s")]));
  event(ctx, { step: "comp-start" });
  const y1 = await settle(ctx, "y1", race([callTarget(ctx, "IdTarget", { label: `${prefix}-y1`, holdMs: 10000 })]));
  const y2 = await settle(ctx, "y2", race([callTarget(ctx, "IdTarget", { label: `${prefix}-y2`, holdMs: 10000 })]));
  const after = await settle(ctx, "after", race([ctx.run("after", counted(ctx, `${prefix}-parent`, "after"))]));
  return { y1, y2, after };
};

// A43: a first cancel interrupts the main wait; compensation issues two steps (distinct keys) and
// awaits each. variant "attach": one-way sends awaited with ctx.attach, one race per tick, and a
// rejected attach is re-attached in the next tick (at most 4 ticks). variant "call": the same two
// steps as request-response calls with the same keys, awaited once each (the negative control).
const attachTick = async (ctx, name, childId) => {
  let outcome;
  for (let tick = 1; tick <= 4; tick++) {
    outcome = await settle(ctx, tick === 1 ? name : `${name}#${tick}`, race([ctx.attach(childId)]));
    if (outcome.settled === "resolved") return { ...outcome, ticks: tick };
  }
  return { ...outcome, ticks: 4 };
};
const callOnce = async (ctx, name, promise) => ({ ...(await settle(ctx, name, race([promise]))), ticks: 1 });
const issueStep = (ctx, variant, step) => {
  if (variant === "call") return { promise: callTarget(ctx, "IdTarget", step.arg, step.key) };
  return { handle: ctx.serviceSendClient(target).apply(step.arg, rpc.sendOpts({ idempotencyKey: step.key })) };
};
const attachThree = async (ctx, { prefix, variant, holdMs, keys }) => {
  begin(ctx, "attachThree");
  await settle(ctx, "x", race([ctx.sleep(60000).map(() => "sleep60s")]));
  event(ctx, { step: "comp-start", variant });
  const steps = keys.map((k, i) => ({ name: `a${i + 1}`, key: k, arg: { label: `${prefix}-c${i + 1}`, preSteps: 1, holdMs } }));
  const issued = steps.map((s) => ({ ...s, ...issueStep(ctx, variant, s) }));
  const results = [];
  for (const s of issued) {
    if (s.handle) event(ctx, { step: `${s.name}:sent`, childId: await s.handle.invocationId });
    const r = s.handle ? await attachTick(ctx, s.name, await s.handle.invocationId) : await callOnce(ctx, s.name, s.promise);
    event(ctx, { ...r, step: `${s.name}:final` });
    results.push(r);
  }
  const after = await settle(ctx, "after", race([ctx.run("after", counted(ctx, `${prefix}-parent`, "after"))]));
  return { results, after };
};

const parent = sdk.service({
  name: "IdParent",
  handlers: { callWithKey, compensate, killDuring, threeCancels, attachThree },
  options: { journalRetention: 3600_000 }
});

const handler = sdk.createEndpointHandler({ services: [target, short, object, leaf, parent] });
const port = Number(process.env.SDK_PORT);
http2.createServer(handler).listen(port, "127.0.0.1", () => {
  console.log("SDK-LISTENING", port, "pid", process.pid);
});
