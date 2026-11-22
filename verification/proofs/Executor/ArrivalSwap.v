(** * Arrival: changing the inputs a function does not read.

    Below the step, the inputs are read only through the persisted journal (by [issue]) and
    the random stream (by [interp]). Two inputs with the same stream give the same result,
    provided the result under the first reports no journal mismatch and the second's
    persisted journal agrees with every command the result issued. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Statements ArrivalBase ArrivalExt.
Import ListNotations.
Open Scope Z_scope.

(** Every command in [t] matches [J]'s persisted command at its index, if there is one. *)
Definition arrival_agree (J : Inputs) (t : list Action) : Prop :=
  forall c k o k', In (ACommand c k o) t -> nth_error (persisted J) c = Some k' ->
  cmd_eqb k k' = true.

Definition arrival_safe (J : Inputs) (t : list Action) : Prop :=
  ~ In (AExit VMismatch) t /\ arrival_agree J t.

Lemma arrival_safe_app : forall J t l, arrival_safe J (t ++ l) -> arrival_safe J t.
Proof.
  intros J t l [H1 H2]. split.
  - intros H. apply H1. apply in_or_app. left. exact H.
  - intros c k o k' H E. apply (H2 c k o k'); [apply in_or_app; left; exact H|exact E].
Qed.

Lemma arrival_ext_safe : forall I J b x y, arrival_ext I b x y ->
  arrival_safe J (trace y) -> arrival_safe J (trace x).
Proof.
  intros I J b x y ((l&E&_)&_) H. rewrite E in H. eapply arrival_safe_app. exact H.
Qed.

Lemma arrival_issue_swap : forall I J x k o s,
  arrival_safe J (trace (issue I x k o s)) -> issue J x k o s = issue I x k o s.
Proof.
  intros I J x k o s [Hm Ha]. revert Hm Ha. unfold issue. cbv zeta.
  destruct (nth_error (persisted I) (next_cmd x)) as [k1|];
    [destruct (cmd_eqb k k1)|];
    [| intros Hm; exfalso; apply Hm; cbn; apply in_or_app; right; left; reflexivity|];
    intros _ Ha; destruct (nth_error (persisted J) (next_cmd x)) as [k2|] eqn:E;
    try reflexivity;
    (rewrite (Ha (next_cmd x) k o k2); [reflexivity| |exact E]);
    cbn; apply in_or_app; right; left; reflexivity.
Qed.

Lemma arrival_issue_op_swap : forall I J x f tok op,
  arrival_safe J (trace (issue_op I x f tok op)) -> issue_op J x f tok op = issue_op I x f tok op.
Proof.
  intros I J x f tok op. unfold issue_op.
  destruct op as [|[d|]]; cbv zeta; [|destruct (split d)|]; apply arrival_issue_swap.
Qed.

(** Split on the innermost match, which is the same on both sides. *)
Ltac arrival_swap_split :=
  repeat match goal with
  | |- context [match ?e with _ => _ end] =>
      lazymatch e with
      | context [match _ with _ => _ end] => fail
      | _ => destruct e
      end
  end.

Lemma arrival_on_start_swap : forall I J x f tok op,
  arrival_safe J (trace (on_start I x f tok op)) -> on_start J x f tok op = on_start I x f tok op.
Proof.
  intros I J x f tok op. unfold on_start. cbv zeta. arrival_swap_split;
    first [reflexivity | apply arrival_issue_op_swap].
Qed.

Lemma arrival_on_event_swap : forall I J x e,
  arrival_safe J (trace (on_event I x e)) -> on_event J x e = on_event I x e.
Proof.
  intros I J x e. unfold on_event.
  destruct (phase x); destruct e; try reflexivity; apply arrival_on_start_swap.
Qed.

Lemma arrival_interp_swap : forall {X} I J (s : Script X) x, stream J = stream I ->
  arrival_safe J (trace (fst (interp I x s))) -> interp J x s = interp I x s.
Proof.
  intros X I J s. induction s as [r|e k IH|f k IH|f k IH|f k IH]; intros x Hst H;
    cbn [interp] in H |- *.
  - reflexivity.
  - assert (E : on_event J x e = on_event I x e).
    { apply arrival_on_event_swap.
      eapply (arrival_ext_safe I J true); [|exact H]. apply arrival_interp_ext. }
    rewrite E. apply IH; assumption.
  - apply IH; assumption.
  - rewrite Hst. apply IH; assumption.
  - apply IH; assumption.
Qed.

Lemma arrival_after_sample_swap : forall I J x a,
  arrival_safe J (trace (after_sample I x a)) -> after_sample J x a = after_sample I x a.
Proof.
  intros I J x a. unfold after_sample.
  destruct a; try reflexivity.
  destruct (link_of rest) as [[]|]; [apply arrival_issue_swap|reflexivity].
Qed.

Lemma arrival_on_notify_swap : forall I J x sb r,
  arrival_safe J (trace (on_notify I x sb r)) -> on_notify J x sb r = on_notify I x sb r.
Proof.
  intros I J x sb r. unfold on_notify, issue_sample.
  destruct sb as [c f tok op k rest|c a|c]; destruct r; try destruct op;
    try destruct a; try reflexivity; try apply arrival_issue_swap;
    cbv zeta; match goal with |- context [phase ?y] => destruct (phase y) end;
    try reflexivity; apply arrival_after_sample_swap.
Qed.

Lemma arrival_on_cancel_swap : forall I J x sb,
  arrival_safe J (trace (on_cancel I x sb)) -> on_cancel J x sb = on_cancel I x sb.
Proof.
  intros I J x sb. unfold on_cancel, issue_sample.
  destruct sb as [c f tok op k rest|c a|c]; try destruct a; try reflexivity;
    apply arrival_issue_swap.
Qed.
