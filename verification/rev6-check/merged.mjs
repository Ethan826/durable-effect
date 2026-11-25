// Exhaustive exploration with sound state merging (issue #48, step 7).
// A node is a model state together with every monitor's state. Two nodes
// with the same model key (model.stateKey, checked by statekey.check.mjs)
// and the same monitor states have the same future and the same verdicts,
// because each monitor's verdict depends only on its state and the items
// still to come (monitors.mjs, checked against predicates.mjs by
// monitors.test.mjs). So a node already explored is skipped.
//
// Pair predicates (S1 to S3 and S10 across two histories) compare whole
// histories and cannot be merged; they run in the sampled tier.
import { createHash } from "node:crypto";
import * as model from "./model.mjs";
import { monitors } from "./monitors.mjs";

const digest = (text) => createHash("sha256").update(text).digest("base64");

// With FREEZE=1 every monitor state is deep-frozen, so a step that writes
// in place to a state shared with another path throws instead of silently
// corrupting it (the monitors use copy-on-write).
const freezing = process.env.FREEZE === "1";
const deepFreeze = (value) => {
  if (value === null || typeof value !== "object" || Object.isFrozen(value)) return value;
  for (const key of Object.keys(value)) deepFreeze(value[key]);
  return Object.freeze(value);
};
const settle = freezing ? deepFreeze : (m) => m;

// Feeds the stream items after `from` to every monitor; returns new states.
const feed = (states, items, from) => {
  let next = states;
  for (let i = from; i < items.length; i += 1) {
    next = next.map((m, k) => settle(monitors[k].step(m, items[i])));
  }
  return next;
};

// UNSOUND_KEY=1 is a control for merged.check.mjs: it merges on the model
// state alone, ignoring the monitors, which can hide failures.
const unsound = process.env.UNSOUND_KEY === "1";
const nodeKey = (state, states) => unsound ? digest(model.stateKey(state))
  : digest(model.stateKey(state) + "\u0000" + JSON.stringify(states));

const verdicts = (states) => states
  .map((m, k) => [monitors[k].id, monitors[k].verdict(m)])
  .filter(([, v]) => v !== null);

// The choice labels from the root to a node, for a witness.
const pathOf = (link) => {
  const labels = [];
  for (let at = link; at !== null; at = at.prev) labels.push(at.choice);
  return labels.reverse();
};

/**
 * Explores one program exhaustively under `options` (model options, e.g.
 * { mutant, limits }). Returns counts, the first witness per failing
 * monitor, and whether `cap` nodes were reached first. `onLeaf(state)` is
 * called for each terminal state explored (each still carries its history).
 */
export const explore = (program, options = {}, cap = Infinity, onLeaf = null) => {
  const seen = new Set();
  const failures = new Map();
  let nodes = 0;
  let leaves = 0;
  const start = model.initial(program, options);
  const items = model.streamOf(start);
  const stack = [{ state: start, states: feed(monitors.map((m) => settle(m.init())), items, 0),
    fed: items.length, link: null }];
  while (stack.length > 0) {
    if (nodes >= cap) return { nodes, leaves, failures, capped: true };
    const { state, states, fed, link } = stack.pop();
    const key = nodeKey(state, states);
    if (seen.has(key)) continue;
    seen.add(key);
    nodes += 1;
    const next = model.choices(state);
    if (next.length === 0) {
      leaves += 1;
      if (onLeaf !== null) onLeaf(state);
      for (const [id, verdict] of verdicts(states)) {
        if (!failures.has(id)) failures.set(id, { verdict, path: pathOf(link) });
      }
      continue;
    }
    for (const choice of next) {
      const child = model.step(state, choice);
      const childItems = model.streamOf(child);
      stack.push({ state: child, states: feed(states, childItems, fed),
        fed: childItems.length, link: { choice, prev: link } });
    }
  }
  return { nodes, leaves, failures, capped: false };
};
