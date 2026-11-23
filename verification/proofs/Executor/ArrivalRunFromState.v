From Coq Require Import List ZArith Bool Arith.
From Durable Require Import Runtime Exec Statements Obligations ArrivalRunFrom StepAwaitTurn.
Import ListNotations.
(** * [RunFromEquivalentState], and S4 for attempts from any equivalent runtime state.

    Adapted from the second independent review's scratch proof (its finding 2). *)

Theorem arrival_run_from_state : RunFromEquivalentState.
Proof.
  unfold RunFromEquivalentState; intros R [HI _] p I Sch r n Hr; unfold start_from.
  exact (proj1 (arrival_iterate_rel R I Sch n {| xs := xs (initial R p I); rs := r |}
                  (initial R p I) HI eq_refl Hr)).
Qed.
(** S4's first clause, for an attempt started from any state equivalent to the initial one. *)
Theorem arrival_s4_from_equivalent : forall R, Meets R -> forall p I Sch r n,
  requiv R r (init R p (seed I)) ->
  let x := xs (iterate R I Sch n (start_from R p I r)) in
  phase x = POpen ->
  (forall f tok op, waiter x = Some (f, tok, op) -> awaiter x = Some (f, tok)) /\
  (forall c f tok op k rest, sub x = Some (SOp c f tok op k rest) -> awaiter x = Some (f, tok)).
Proof.
  intros R HM p I Sch r n Hr x; unfold x; rewrite (arrival_run_from_state R HM p I Sch r n Hr).
  apply (proj1 step_s4 R HM p I Sch); exists n; reflexivity.
Qed.
