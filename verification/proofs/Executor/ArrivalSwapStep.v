(** * Arrival: changing the inputs a step does not read.

    Under [arrival_sinf], a step reads the foreign input at the current progress count, the
    journal entry at the cursor, and what the functions below it read (ArrivalSwap.v). With
    those the same, two inputs give the same step. A step that consumes no entry gives the
    same step whatever the entries, unless it waits for good under the first input. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Statements ArrivalBase ArrivalExt ArrivalGrow
  ArrivalSwap.
Import ListNotations.
Open Scope Z_scope.

Lemma arrival_at_boundary_sub_cursor : forall I Sch x sb y,
  at_boundary_sub I Sch x sb = Some y -> cursor y = S (cursor x).
Proof.
  intros I Sch x sb y H. unfold at_boundary_sub in H.
  destruct (arrived Sch (micro x) <=? cursor x)%nat; [discriminate|].
  destruct (nth_error (entries I) (cursor x)) as [[c r|]|]; [| |discriminate].
  - destruct (Nat.eqb c (sub_cmd sb)).
    + injection H as <-. destruct (arrival_on_notify_ext I (set_cursor x (S (cursor x))) sb r)
        as (_&_&_&_&U&_). rewrite U. reflexivity.
    + destruct (c <? next_cmd x)%nat; [|discriminate]. injection H as <-. reflexivity.
  - injection H as <-. destruct (arrival_on_cancel_ext I (set_cursor x (S (cursor x))) sb)
      as (_&_&_&_&U&_). rewrite U. reflexivity.
Qed.

Lemma arrival_at_boundary_sub_swap : forall I J x sb,
  (forall y, at_boundary_sub I (arrival_sinf I) x sb = Some y -> arrival_safe J (trace y)) ->
  nth_error (entries J) (cursor x) = nth_error (entries I) (cursor x) ->
  at_boundary_sub J (arrival_sinf J) x sb = at_boundary_sub I (arrival_sinf I) x sb.
Proof.
  intros I J x sb H EJ. unfold at_boundary_sub in *. cbn [arrival_sinf arrived] in *.
  destruct (nth_error (entries I) (cursor x)) as [e|] eqn:EI.
  - assert (LI : (cursor x < length (entries I))%nat)
      by (apply nth_error_Some; congruence).
    assert (LJ : (cursor x < length (entries J))%nat)
      by (apply nth_error_Some; congruence).
    replace (length (entries I) <=? cursor x)%nat with false in *
      by (symmetry; apply Nat.leb_gt; exact LI).
    replace (length (entries J) <=? cursor x)%nat with false
      by (symmetry; apply Nat.leb_gt; exact LJ).
    rewrite EJ. destruct e as [c r|].
    + destruct (Nat.eqb c (sub_cmd sb)); [|reflexivity].
      f_equal. apply arrival_on_notify_swap. apply H. reflexivity.
    + f_equal. apply arrival_on_cancel_swap. apply H. reflexivity.
  - apply nth_error_None in EI. pose proof EJ as EJ'. apply nth_error_None in EJ'.
    replace (length (entries I) <=? cursor x)%nat with true by (symmetry; apply Nat.leb_le; lia).
    replace (length (entries J) <=? cursor x)%nat with true by (symmetry; apply Nat.leb_le; lia).
    reflexivity.
Qed.

Lemma arrival_at_boundary_swap : forall I J x,
  (forall y, at_boundary I (arrival_sinf I) x = Some y -> arrival_safe J (trace y)) ->
  (nth_error (entries J) (cursor x) = nth_error (entries I) (cursor x) ->
   at_boundary J (arrival_sinf J) x = at_boundary I (arrival_sinf I) x) /\
  (forall y, at_boundary I (arrival_sinf I) x = Some y -> cursor y = cursor x ->
   at_boundary J (arrival_sinf J) x = Some y).
Proof.
  intros I J x H. unfold at_boundary in *.
  destruct (phase x);
    [|split; [reflexivity|intros y Hy _; exact Hy]
     |split; [reflexivity|intros y Hy; discriminate]].
  assert (Sub : forall sb, (forall y, at_boundary_sub I (arrival_sinf I) x sb = Some y ->
                              arrival_safe J (trace y)) ->
     (nth_error (entries J) (cursor x) = nth_error (entries I) (cursor x) ->
      at_boundary_sub J (arrival_sinf J) x sb = at_boundary_sub I (arrival_sinf I) x sb) /\
     (forall y, at_boundary_sub I (arrival_sinf I) x sb = Some y -> cursor y = cursor x ->
      at_boundary_sub J (arrival_sinf J) x sb = Some y)).
  { intros sb Hsb. split; [intros EJ; apply arrival_at_boundary_sub_swap; assumption|].
    intros y Hy Hc. apply arrival_at_boundary_sub_cursor in Hy. lia. }
  destruct (held x), (waiter x) as [[[f tok] op]|].
  - split; [reflexivity|intros y Hy _; exact Hy].
  - destruct (sub x) as [sb|]; [apply Sub; exact H|].
    split; [reflexivity|intros y Hy _; exact Hy].
  - destruct (sub x) as [sb|]; [apply Sub; exact H|].
    split; [intros _; f_equal; apply arrival_issue_op_swap; apply H; reflexivity|].
    intros y Hy _. rewrite <- Hy. f_equal. apply arrival_issue_op_swap. apply H. reflexivity.
  - destruct (sub x) as [sb|]; [apply Sub; exact H|].
    split; [reflexivity|intros y Hy _; exact Hy].
Qed.

Lemma arrival_step_swap : forall R I J s, stream J = stream I ->
  foreign J (progress (xs s)) = foreign I (progress (xs s)) ->
  arrival_safe J (trace (xs (step R I (arrival_sinf I) s))) ->
  (nth_error (entries J) (cursor (xs s)) = nth_error (entries I) (cursor (xs s)) ->
   step R J (arrival_sinf J) s = step R I (arrival_sinf I) s) /\
  (cursor (xs (step R I (arrival_sinf I) s)) = cursor (xs s) ->
   step R I (arrival_sinf I) s = arrival_bump s \/
   step R J (arrival_sinf J) s = step R I (arrival_sinf I) s).
Proof.
  intros R I J [x r] Hst Hf Hs. cbn [xs] in Hf. revert Hs. unfold step. cbn [xs rs].
  assert (Ef : foreign_due J x = foreign_due I x).
  { unfold foreign_due. destruct (fseen x); [destruct (Nat.eqb n (progress x))|];
      congruence. }
  rewrite Ef.
  destruct (phase x); [| |intros _; split; [reflexivity|right; reflexivity]];
    cbn [stop_due cut_due arrival_sinf stop_at cut_at];
    (destruct (foreign_due I x); [intros _; split; [reflexivity|right; reflexivity]|]);
    (destruct (queue x) as [|t rest]).
  2, 4: rewrite !arrival_run_head_unfold;
    set (x2 := arrival_pre (set_progress (set_queue x rest) (S (progress x))) t);
    destruct (interp I x2 (run_task R r t)) as [a b] eqn:E; cbn [xs]; intros Hs;
    rewrite (arrival_interp_swap I J); [rewrite E; split; [reflexivity|right; reflexivity]
                                       |exact Hst|rewrite E; exact Hs].
  all: intros Hs; destruct (arrival_at_boundary_swap I J x) as [B1 B2];
    [intros y Hy; rewrite Hy in Hs; exact Hs|].
  all: split; [intros EJ; rewrite (B1 EJ); reflexivity|].
  all: destruct (at_boundary I (arrival_sinf I) x) as [y|] eqn:Hb;
    [|intros _; left; reflexivity].
  all: cbn [xs]; intros Hc; right; rewrite (B2 y eq_refl Hc); reflexivity.
Qed.
