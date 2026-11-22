(** * P3, P7, P8 and P9, from the invariant of [TimeA].

    Each claim is a fact about the trace before a delivery or a cancellation, which the
    invariant records as the trace grows. They take as a hypothesis [time_fresh_tokens]:
    a trace starts no token twice, which is I4's second half carried from the runtime's log
    to the executor's trace. *)

From Coq Require Import List ZArith Bool Arith Lia Sorting.
From Durable Require Import Runtime Exec Rev3 Statements TimeBase TimeStep TimeL TimeA
  TimeA2 TimeA3.
Import ListNotations.
Open Scope Z_scope.

Lemma time_inva_initial : forall R p I, time_inva (xs (initial R p I)).
Proof.
  intros R p I. unfold initial. tsimp.
  destruct (time_issue_sample_cases I
    (mk POpen [] None None None false 0 0 0 0 [] None false [] 0 0 None) FInitial) as [-> | ->].
  all: try unfold finish; constructor; tsimp; try (intros; contradiction); try discriminate.
  all: try (intros f tok; unfold time_ldinv; cbn; exact Logic.I).
  all: try (apply time_claims_snoc; [apply time_claims_nil|exact Logic.I]).
  all: intros f tok H; cbn in H; discriminate.
Qed.

(** The invariant holds of every reachable state of an attempt whose traces start no token
    twice. *)
Lemma time_inva_run : forall R p I Sch,
  (forall n, NoDup (time_stoks (run R p I Sch n))) ->
  forall n, time_inva (xs (iterate R I Sch n (initial R p I))).
Proof.
  intros R p I Sch N n. induction n as [|n IH]; [apply time_inva_initial|].
  rewrite time_iterate_S. apply time_inva_step; [exact IH|apply time_invl_run|].
  rewrite <- time_iterate_S. exact (N (S n)).
Qed.

Lemma time_claims_run : forall R p I Sch n,
  (forall n, NoDup (time_stoks (run R p I Sch n))) ->
  time_claims time_claim_at (run R p I Sch n).
Proof.
  intros R p I Sch n N. exact (ta_claims _ (time_inva_run R p I Sch N n)).
Qed.

Lemma time_existsb_false_not_in : forall (p : Action -> bool) t a,
  existsb p t = false -> p a = true -> ~ In a t.
Proof.
  intros p t a H Ha I0. assert (existsb p t = true) by (apply existsb_exists; eauto).
  congruence.
Qed.

Lemma time_starts_dec : forall f tok mid,
  starts f tok mid \/ existsb (time_is_start f tok) mid = false.
Proof.
  intros f tok mid. destruct (existsb (time_is_start f tok) mid) eqn:E; [left|right; reflexivity].
  apply existsb_exists in E as [a [Ia Ha]]. destruct a; try discriminate.
  apply time_eqb_pair in Ha as [-> ->]. exists op. exact Ia.
Qed.

Lemma time_not_starts : forall f tok mid,
  ~ starts f tok mid -> existsb (time_is_start f tok) mid = false.
Proof.
  intros f tok mid H. destruct (time_starts_dec f tok mid) as [S|S]; [contradiction|exact S].
Qed.

Lemma time_no_owned : forall f tok pre2,
  (forall c' k', ~ In (ACommand c' k' (Some (f, tok))) pre2) ->
  existsb (time_is_owned f tok) pre2 = false.
Proof.
  intros f tok pre2 H. destruct (existsb (time_is_owned f tok) pre2) eqn:E; [|reflexivity].
  apply existsb_exists in E as [a [Ia Ha]].
  destruct a as [| c k [[f' tok']|] | | | | | | | | |]; try discriminate.
  apply time_eqb_pair in Ha as [-> ->]. exfalso. exact (H c k Ia).
Qed.

Lemma time_sample_in : forall t,
  existsb time_is_sample t = true -> exists c s l cr, In (ASampled c s l cr) t.
Proof.
  intros t H. apply existsb_exists in H as [a [Ia Ha]]. destruct a; try discriminate. eauto.
Qed.

(** ** The claims, given that no token is started twice *)

Theorem time_p3_of : time_fresh_tokens -> P3.
Proof.
  intros U R HR p I Sch n pre mid post f tok d o E Ns Hd.
  pose proof (time_claims_run R p I Sch n (U R HR p I Sch)) as C.
  rewrite E in C. specialize (C (pre ++ AStart f tok (OSleep (Millis d)) :: mid)
    (ADelivered f tok o) post ltac:(rewrite <- app_assoc; reflexivity)).
  destruct C as [C _]. unfold time_p3_ok in C.
  rewrite time_after_last_app in C; [| cbn; rewrite !Nat.eqb_refl; reflexivity
    |apply time_not_starts; exact Ns].
  exact (C Hd).
Qed.

Theorem time_p9_of : time_fresh_tokens -> P9.
Proof.
  intros U R HR p I Sch n pre mid post f tok o E.
  destruct (time_starts_dec f tok mid) as [S|Ns]; [exact S|exfalso].
  pose proof (time_claims_run R p I Sch n (U R HR p I Sch)) as C.
  rewrite E in C. specialize (C (pre ++ AStart f tok (OSleep Forever) :: mid)
    (ADelivered f tok o) post ltac:(rewrite <- app_assoc; reflexivity)).
  destruct C as [C _]. unfold time_p3_ok in C.
  rewrite time_after_last_app in C; [exact C|cbn; rewrite !Nat.eqb_refl; reflexivity|exact Ns].
Qed.

Theorem time_p7_of : time_fresh_tokens -> P7.
Proof.
  intros U R HR p I Sch n pre f tok o post pre1 c k pre2 E Ep No.
  pose proof (time_claims_run R p I Sch n (U R HR p I Sch)) as C.
  rewrite E in C. destruct (C pre (ADelivered f tok o) post eq_refl) as [_ C7].
  unfold time_p7_ok in C7. rewrite Ep, time_after_last_app in C7;
    [|cbn; rewrite !Nat.eqb_refl; reflexivity|apply time_no_owned; exact No].
  destruct (time_sample_in pre2 C7) as [c' [s [l [cr Ii]]]]. eauto.
Qed.

Theorem time_p8_of : time_fresh_tokens -> P8.
Proof.
  intros U. split.
  - intros R HR p I Sch n pre f tok post pre1 c k pre2 E Ep No.
    pose proof (time_claims_run R p I Sch n (U R HR p I Sch)) as C.
    rewrite E in C. destruct (C pre (ACancelled f tok) post eq_refl) as [Ca _].
    unfold time_p8a_ok in Ca. rewrite Ep, time_after_last_app in Ca;
      [|cbn; rewrite !Nat.eqb_refl; reflexivity|apply time_no_owned; exact No].
    destruct Ca as [Pl Cr]. split; [|exact Cr].
    apply existsb_exists in Pl as [a [Ia Ha]].
    destruct a as [| | c' s l [[[? ?] ?]|] | | | | | | | |]; try discriminate. eauto.
  - intros R HR p I Sch n pre f tok op post pre1 pre2 E Ep Ns Nc c' s l cr Ii.
    pose proof (time_claims_run R p I Sch n (U R HR p I Sch)) as C.
    rewrite E in C. destruct (C pre (ACancelled f tok) post eq_refl) as [_ Cb].
    unfold time_p8b_ok in Cb. rewrite Ep, time_after_last_app in Cb;
      [|cbn; rewrite !Nat.eqb_refl; reflexivity|apply time_not_starts; exact Ns].
    assert (Hc : existsb time_is_cmd pre2 = false).
    { destruct (existsb time_is_cmd pre2) eqn:Ec; [|reflexivity].
      apply existsb_exists in Ec as [a [Ia Ha]]. destruct a; try discriminate.
      exfalso. exact (Nc _ _ _ Ia). }
    specialize (Cb Hc). eapply time_existsb_false_not_in; [exact Cb| |exact Ii]. reflexivity.
Qed.
