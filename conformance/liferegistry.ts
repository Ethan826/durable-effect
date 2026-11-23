import { guardMutants } from "./guardmutants.ts";
import { lifeMutants } from "./lifemutants.ts";
import type { LifecycleMutant, LifecycleProperty, Variant } from "./mutants.ts";

const lifecycleOf = (
  property: LifecycleProperty,
  make: Variant,
): LifecycleMutant => ({ property, make });

/**
 * Each mutant #37's table lists for I3, I4, I5, I6 and I8, by name, with
 * two more the review asked for: `actsOnResume` (I3, an executor action
 * after a foreign resume) and `maskAll` (I4, every await treated as
 * masked). They live in guardmutants.ts (I3) and lifemutants.ts.
 */
export const lifecycleMutants = {
  preventYield: lifecycleOf("I3", guardMutants.preventYield),
  runsContinuation: lifecycleOf("I3", guardMutants.runsContinuation),
  withoutWrapper: lifecycleOf("I3", guardMutants.withoutWrapper),
  recordsThenForwards: lifecycleOf("I3", guardMutants.recordsThenForwards),
  actsOnResume: lifecycleOf("I3", guardMutants.actsOnResume),
  releaseAfterCleanup: lifecycleOf("I4", lifeMutants.releaseAfterCleanup),
  neverReleases: lifecycleOf("I4", lifeMutants.neverReleases),
  releaseAtRequest: lifecycleOf("I4", lifeMutants.releaseAtRequest),
  maskAll: lifecycleOf("I4", lifeMutants.maskAll),
  privateQueue: lifecycleOf("I5", lifeMutants.privateQueue),
  exitBeforeCleanup: lifecycleOf("I6", lifeMutants.exitBeforeCleanup),
  omitDetached: lifecycleOf("I8", lifeMutants.omitDetached),
  omitInternal: lifecycleOf("I8", lifeMutants.omitInternal),
} as const;

/** A lifecycle mutant's name. */
export type LifecycleMutantName = keyof typeof lifecycleMutants;
