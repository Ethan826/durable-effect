(** * P2, P4, P5 and P6, from the invariant of [TimeL].

    Each follows from the shape of the applied samples alone: the first sets [L] to its
    reading, and each later one sets [L] to the larger of [L] plus its chunk and its
    reading. *)

From Coq Require Import List ZArith Bool Arith Lia Sorting.
From Durable Require Import Runtime Exec Rev3 Statements TimeBase TimeStep TimeL.
Import ListNotations.
Open Scope Z_scope.

(** ** Facts about a list of the right shape *)

Lemma time_shape_chunk : forall a i e,
  time_shape a -> nth_error a i = Some e -> 0 <= chunk e.
Proof.
  intros a i e [H0 [HS _]] H. destruct i as [|j].
  - rewrite (proj2 (H0 e H)). lia.
  - destruct (nth_error a j) as [e0|] eqn:E0.
    + exact (proj2 (HS j e0 e E0 H)).
    + apply nth_error_None in E0. assert (nth_error a (S j) <> None) by congruence.
      apply nth_error_Some in H1. lia.
Qed.

Lemma time_shape_prev : forall (a : list (Z * Z * Z)) j e,
  nth_error a (S j) = Some e -> exists e0, nth_error a j = Some e0.
Proof.
  intros a j e H. destruct (nth_error a j) as [e0|] eqn:E0; [eauto|].
  apply nth_error_None in E0. assert (nth_error a (S j) <> None) by congruence.
  apply nth_error_Some in H0. lia.
Qed.

Lemma time_shape_reading : forall a i e,
  time_shape a -> nth_error a i = Some e -> reading e <= lafter e.
Proof.
  intros a i e Hs H. destruct Hs as [H0 [HS HM]]. destruct i as [|j].
  - rewrite (proj1 (H0 e H)). lia.
  - destruct (time_shape_prev a j e H) as [e0 E0].
    rewrite (proj1 (HS j e0 e E0 H)). lia.
Qed.

Lemma time_firstn_snoc : forall (a : list (Z * Z * Z)) i e,
  nth_error a i = Some e -> firstn (S i) a = firstn i a ++ [e].
Proof.
  intros a. induction a as [|b a IH]; intros i e H; [destruct i; discriminate|].
  destruct i as [|i]; cbn in H.
  - inversion H; reflexivity.
  - change (firstn (S (S i)) (b :: a)) with (b :: firstn (S i) a).
    change (firstn (S i) (b :: a)) with (b :: firstn i a).
    rewrite (IH i e H). reflexivity.
Qed.

Lemma time_max_snoc : forall l b r,
  fold_right Z.max b (l ++ [r]) = Z.max (fold_right Z.max b l) r.
Proof.
  intros l b r. induction l as [|x l IH]; cbn; [lia|]. rewrite IH. lia.
Qed.

Lemma time_add_snoc : forall l r,
  fold_right Z.add 0 (l ++ [r]) = fold_right Z.add 0 l + r.
Proof.
  intros l r. induction l as [|x l IH]; cbn; [lia|]. rewrite IH. lia.
Qed.

Lemma time_max_ge_base : forall l b, b <= fold_right Z.max b l.
Proof. intros l b. induction l as [|x l IH]; cbn; lia. Qed.

(** P6's bounds, for every applied sample, by induction on its position. *)
Lemma time_shape_p6 : forall a first,
  time_shape a -> nth_error a 0 = Some first ->
  forall i e, nth_error a i = Some e ->
    reading first <= lafter e /\
    lafter e <= fold_right Z.max (reading first) (map reading (firstn (S i) a)) +
                fold_right Z.add 0 (map chunk (firstn (S i) a)) /\
    0 <= fold_right Z.add 0 (map chunk (firstn (S i) a)).
Proof.
  intros a first Hs H0 i. induction i as [|j IH]; intros e H.
  - rewrite H0 in H. inversion H; subst.
    rewrite (time_firstn_snoc a 0 e H0). cbn.
    destruct (proj1 Hs e H0) as [L C]. rewrite L, C. lia.
  - destruct (time_shape_prev a j e H) as [e0 E0].
    destruct (IH e0 E0) as [A [B C]].
    rewrite (time_firstn_snoc a (S j) e H), !map_app. cbn [map].
    rewrite time_max_snoc, time_add_snoc.
    destruct (proj1 (proj2 Hs) j e0 e E0 H) as [L Ch]. rewrite L. cbn [map]. lia.
Qed.

(** P5's bound, by induction on the position of the sample. *)
Lemma time_shape_p5 : forall a (truth : nat -> Z) E lead,
  time_shape a -> 0 <= lead ->
  (forall i e, nth_error a i = Some e -> reading e <= truth i + E) ->
  (forall i, truth i <= truth (S i)) ->
  (forall i e, nth_error a (S i) = Some e -> 0 < chunk e ->
     truth i + chunk e - lead <= truth (S i)) ->
  forall i e, nth_error a i = Some e ->
    lafter e <= truth i + E +
      lead * Z.of_nat (length (filter (fun e' => 0 <? chunk e') (firstn (S i) a))).
Proof.
  intros a truth E lead Hs Hl Hr Ht Hk i. induction i as [|j IH]; intros e H.
  - destruct (proj1 Hs e H) as [L _]. rewrite L.
    pose proof (Hr 0%nat e H).
    assert (0 <= lead * Z.of_nat
      (length (filter (fun e' => 0 <? chunk e') (firstn 1 a)))) by (apply Z.mul_nonneg_nonneg; lia).
    lia.
  - destruct (time_shape_prev a j e H) as [e0 E0].
    pose proof (IH e0 E0) as I0.
    rewrite (time_firstn_snoc a (S j) e H), filter_app, length_app.
    set (m := length (filter (fun e' => 0 <? chunk e') (firstn (S j) a))) in *.
    destruct (proj1 (proj2 Hs) j e0 e E0 H) as [L Ch]. rewrite L.
    pose proof (Hr (S j) e H). pose proof (Ht j).
    assert (Hm : 0 <= lead * Z.of_nat m) by (apply Z.mul_nonneg_nonneg; lia).
    cbn [filter]. destruct (0 <? chunk e) eqn:Pc.
    + apply Z.ltb_lt in Pc. pose proof (Hk j e H Pc). cbn [length].
      rewrite Nat2Z.inj_add, Z.mul_add_distr_l. cbn [Z.of_nat Pos.of_succ_nat].
      set (M := lead * Z.of_nat m) in *. lia.
    + apply Z.ltb_ge in Pc. cbn [length]. rewrite Nat.add_0_r.
      set (M := lead * Z.of_nat m) in *. lia.
Qed.

(** ** The claims *)

Theorem time_p2 : P2.
Proof.
  intros R _ p I Sch n. unfold run. apply (tl_sorted _ (time_invl_run R p I Sch n)).
Qed.

Theorem time_p4 : P4.
Proof.
  intros R _ p I Sch n e H. apply In_nth_error in H as [i H].
  eapply time_shape_reading; [|exact H]. apply (tl_shape _ (time_invl_run R p I Sch n)).
Qed.

Theorem time_p5 : P5.
Proof.
  intros R _ p I Sch n truth E lead a Hl Hr Ht Hk i e H.
  apply (time_shape_p5 a truth E lead); auto.
  apply (tl_shape _ (time_invl_run R p I Sch n)).
Qed.

Theorem time_p6 : P6.
Proof.
  intros R _ p I Sch n i e first a H0 H.
  pose proof (tl_shape _ (time_invl_run R p I Sch n)) as Hs. fold a in Hs.
  destruct (time_shape_p6 a first Hs H0 i e H) as [A [B _]].
  split; [exact A|]. split; [exact B|].
  apply (proj2 (proj2 Hs)). eapply nth_error_In. exact H.
Qed.
