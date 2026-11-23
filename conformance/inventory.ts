/**
 * What is wrong with an inventory: it is empty, or a required kind was
 * never seen. An empty inventory is a gap of its own, so a gate over
 * nothing cannot pass.
 */
export const inventoryGaps = (
  required: ReadonlyArray<string>,
  seen: ReadonlySet<string>,
): ReadonlyArray<string> =>
  required.length === 0
    ? ["the grammar inventory is empty"]
    : required.filter((kind) => !seen.has(kind)).map((kind) => `no ${kind}`);
