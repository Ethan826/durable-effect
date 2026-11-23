(** * RunFromEquivalent: a run from an equivalent runtime state has the same trace.

    Under one schedule, a step from equivalent runtime states gives the same executor state
    and equivalent runtime states (I1, through [arrival_step_rel]). By induction on the
    number of steps, a run started from any state equivalent to [init] keeps the executor
    state of [run] at every step, so the statements stated from the initial state hold for
    attempts in any process. *)

From Coq Require Import List ZArith Bool Arith.
From Durable Require Import Runtime Exec Statements Obligations ArrivalSim.
Import ListNotations.
Open Scope Z_scope.

Lemma arrival_iterate_rel : forall R I Sch n s1 s2, I1 R ->
  xs s1 = xs s2 -> requiv R (rs s1) (rs s2) ->
  xs (iterate R I Sch n s1) = xs (iterate R I Sch n s2) /\
  requiv R (rs (iterate R I Sch n s1)) (rs (iterate R I Sch n s2)).
Proof.
  intros R I Sch n. induction n as [|n IH]; intros [x1 r1] [x2 r2] HI Ex Er;
    cbn [xs rs] in Ex, Er; [split; assumption|].
  subst x2. cbn [iterate].
  destruct (arrival_step_rel R I Sch x1 r1 r2 HI Er) as [E Q].
  apply IH; assumption.
Qed.

Theorem arrival_run_from_equivalent : RunFromEquivalent.
Proof.
  intros R [HI _] p I Sch r n Hr. unfold run_from, run, start_from.
  destruct (arrival_iterate_rel R I Sch n
              {| xs := xs (initial R p I); rs := r |} (initial R p I) HI eq_refl Hr)
    as [E _].
  rewrite E. reflexivity.
Qed.
