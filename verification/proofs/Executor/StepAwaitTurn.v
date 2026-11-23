(** * Step domain: the awaiter invariant at turn boundaries, over a run, and S4. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Statements StepInv StepTurn StepLog StepAwait.
Import ListNotations.
Open Scope Z_scope.

(** ** Helpers *)

(** A state whose subscription is empty and whose queue holds no new delivery. *)
Lemma step_ainv_sub_none : forall L x y, AInv L x -> sub y = None ->
  awaiter y = awaiter x -> waiter y = waiter x ->
  (forall t, In t (queue y) -> In t (queue x) \/ dpair t = None) -> AInv L y.
Proof.
  intros L x y [A B C D E F] Hs Ha Hw Hq; constructor; rewrite ?Ha, ?Hw, ?Hs; auto;
    try discriminate.
  intros t f tok Ht Hd; destruct (Hq t Ht) as [Ht1 | Hn]; [| congruence].
    destruct (F t f tok Ht1 Hd) as [G1 G2]; split; auto.
    intros Ha'; destruct (G2 Ha'); split; cbn; auto.
Qed.

(** The waiter is [None] when an operation or awaited sample is subscribed. *)
Lemma step_waiter_none : forall L x, AInv L x ->
  (not_sop (sub x) -> False) \/ follows_pair (sub x) <> None -> waiter x = None.
Proof.
  intros L x AI H; destruct (waiter x) eqn:W; auto.
  destruct (a_slot _ _ AI) as [S0 | S0]; [congruence | |].
  - destruct H as [H | H]; rewrite S0 in H; cbn in H; [tauto | congruence].
  - destruct H as [H | H];
      [exfalso; apply H, step_slot_not_sop; auto | rewrite step_slot_follows in H; auto;
       congruence].
Qed.

(** A sample issued for the awaiting fiber, at a turn boundary. *)
Lemma step_sinv_issue_sample : forall I L x a f tok, AInv L x ->
  awaiter x = Some (f, tok) -> waiter x = None -> queue x = [] ->
  follows_pair (Some (SSample 0 a)) = Some (f, tok) -> ASInv L (issue_sample I x a).
Proof.
  intros I L x a f tok AI Ha Hw Hq Hf Py.
  destruct (step_issue_sample_stays _ _ _ Py) as (H1 & H2 & H3 & _ & c & H4).
  constructor; rewrite ?H1, ?H2, ?H3, ?H4, ?Hw, ?Hq; try discriminate.
  - intros f' tok' H; rewrite Ha; destruct a; cbn in Hf, H; congruence.
  - intros H; exfalso; apply H; reflexivity.
  - exact (a_tok _ _ AI).
  - intros t f' tok' [].
Qed.

(** A delivery queued once an awaited sample is applied. *)
Lemma step_ainv_deliver : forall L x y f tok t, AInv L x ->
  follows_pair (sub x) = Some (f, tok) -> sub y = None -> awaiter y = awaiter x ->
  waiter y = waiter x -> queue y = [t] -> dpair t = Some (f, tok) -> AInv L y.
Proof.
  intros L x y f tok t AI Hf Hs Ha Hw Hq Hd.
  assert (Ha' : awaiter x = Some (f, tok)) by exact (a_sample _ _ AI f tok Hf).
  assert (Hw' : waiter x = None) by (apply (step_waiter_none L); auto; right; congruence).
  constructor; rewrite ?Ha, ?Hw, ?Hs, ?Hq, ?Hw'; try discriminate.
  - intros _; left; reflexivity.
  - exact (a_tok _ _ AI).
  - intros t' f' tok' [Ht | []] Hd'; subst t'; rewrite Hd in Hd'; inversion Hd'; subst.
    split; [exact (a_tok _ _ AI f' tok' Ha') | cbn; auto].
Qed.

(** ** Notifications and cancellations *)

Lemma step_sinv_after_sample : forall I L x y after, AInv L x -> queue x = [] ->
  sub x = Some (SSample 0 after) \/ (exists c, sub x = Some (SSample c after)) ->
  sub y = None -> awaiter y = awaiter x -> waiter y = waiter x -> queue y = queue x ->
  phase y = POpen -> ASInv L (after_sample I y after).
Proof.
  intros I L x y after AI Q HS Hs Ha Hw Hq P Py.
  assert (HS' : exists c, sub x = Some (SSample c after)) by (destruct HS as [H | H]; eauto).
  destruct HS' as [c S0].
  destruct after as [| f tok o | f tok k rest | f tok | f tok k]; cbn [after_sample] in *.
  - apply (step_ainv_sub_none L x); fields; auto.
    intros t Ht; rewrite Hq, Q in Ht; destruct Ht as [<- | []]; auto.
  - apply (step_ainv_deliver L x _ f tok (Deliver f tok o)); fields; rewrite ?Hq, ?Q, ?S0;
      auto.
  - destruct (link_of rest) as [[chunk rest'] |].
    + assert (Ha' : awaiter x = Some (f, tok))
        by (apply (a_sample _ _ AI); rewrite S0; reflexivity).
      assert (Hw' : waiter x = None)
        by (apply (step_waiter_none L); auto; right; rewrite S0; discriminate).
      destruct (step_issue_stays _ _ _ _ _ Py) as (H1 & H2 & H3 & _ & _ & H4).
      constructor; rewrite ?H1, ?H2, ?H3, ?H4, ?Ha, ?Hw, ?Hw', ?Hq, ?Q; try discriminate.
      * intros c' f' tok' op' k' r' E; inversion E; subst; auto.
      * intros H; exfalso; apply H; reflexivity.
      * exact (a_tok _ _ AI).
      * intros t f' tok' [].
    + apply (step_ainv_deliver L x _ f tok (Deliver f tok (Value 0))); fields;
        rewrite ?Hq, ?Q, ?S0; auto.
  - apply (step_ainv_deliver L x _ f tok (DeliverCancel f tok)); fields; rewrite ?Hq, ?Q, ?S0;
      auto.
  - apply (step_ainv_sub_none L x); auto.
    intros t Ht; rewrite Hq in Ht; auto.
Qed.

Lemma step_sinv_on_notify : forall I L x s r, Inv x -> AInv L x -> phase x = POpen ->
  queue x = [] -> sub x = Some s -> ASInv L (on_notify I x s r).
Proof.
  intros I L x s r HI AI P Q S0.
  assert (Hv : violated x = false).
  { destruct (violated x) eqn:V; auto; exfalso; exact (inv_viol _ HI V P). }
  assert (SI : ASInv L x) by (intros _; exact AI).
  destruct s as [c f tok op k rest | c after | c]; unfold on_notify.
  - assert (Ha : awaiter x = Some (f, tok)) by exact (a_sop _ _ AI c f tok op k rest S0).
    assert (Hw : waiter x = None)
      by (apply (step_waiter_none L); auto; left; rewrite S0; cbn; auto).
    destruct op as [kk aa | d], r as [o | v |]; auto;
      apply (step_sinv_issue_sample I L x _ f tok); auto.
  - destruct r as [o | v |].
    + destruct after; auto; intros Py; apply (step_ainv_sub_none L x); fields; auto.
    + destruct after as [| f tok o | f tok kk rest | f tok | f tok kk];
        [| | | | intros Py; apply (step_ainv_sub_none L x); fields; auto];
      (cbv zeta; match goal with |- ASInv L (match phase (apply_sample ?x ?c ?v ?a) with
                                            | POpen => _ | _ => _ end) =>
        destruct (step_apply_sample_cases x c v a) as [E | (a' & l & Ha' & E)]; rewrite E;
        [destruct (step_violate_open x Overflow P Hv) as [Hp _]; rewrite Hp;
         intros Py; rewrite Hp in Py; discriminate |]
       end);
      fields; rewrite P;
      (apply (step_sinv_after_sample I L x); fields; auto; right; eauto).
    + destruct after; try (intros Py; apply (step_ainv_sub_none L x); fields; auto; fail);
        intros Py; rewrite (step_violate_stays _ _ Py); auto.
  - intros Py; apply (step_ainv_sub_none L x); fields; auto.
Qed.

Lemma step_sinv_on_cancel : forall I L x s, Inv x -> AInv L x -> phase x = POpen ->
  queue x = [] -> sub x = Some s -> ASInv L (on_cancel I x s).
Proof.
  intros I L x s HI AI P Q S0.
  destruct s as [c f tok op k rest | c after | c]; cbn [on_cancel].
  - assert (Ha : awaiter x = Some (f, tok)) by exact (a_sop _ _ AI c f tok op k rest S0).
    assert (Hw : waiter x = None)
      by (apply (step_waiter_none L); auto; left; rewrite S0; cbn; auto).
    apply (step_sinv_issue_sample I L x _ f tok); auto.
  - destruct after as [| f tok o | f tok kk rest | f tok | f tok kk].
    + intros Py; destruct (step_issue_sample_stays _ _ _ Py) as (H1 & H2 & H3 & _ & c' & H4).
      assert (Hsl : slot_held (issue_sample I (set_held x true) FInitial) = true)
        by (unfold slot_held; rewrite H4; reflexivity).
      constructor; rewrite ?H1, ?H2, ?H3, ?H4; fields; rewrite ?Q; try discriminate.
      * exact (a_waiter _ _ AI).
      * intros _; right; exact Hsl.
      * exact (a_tok _ _ AI).
      * intros t f' tok' [].
    + apply (step_sinv_issue_sample I L x _ f tok); auto;
        [apply (a_sample _ _ AI); rewrite S0; reflexivity |
         apply (step_waiter_none L); auto; right; rewrite S0; discriminate].
    + apply (step_sinv_issue_sample I L x _ f tok); auto;
        [apply (a_sample _ _ AI); rewrite S0; reflexivity |
         apply (step_waiter_none L); auto; right; rewrite S0; discriminate].
    + apply (step_sinv_issue_sample I L x _ f tok); auto;
        [apply (a_sample _ _ AI); rewrite S0; reflexivity |
         apply (step_waiter_none L); auto; right; rewrite S0; discriminate].
    + intros Py; apply (step_ainv_sub_none L x); fields; auto.
  - intros Py; apply (step_ainv_sub_none L x); fields; auto.
Qed.

Lemma step_asinv_boundary : forall I Sch L x y, Inv x -> AInv L x -> phase x = POpen ->
  queue x = [] -> at_boundary I Sch x = Some y -> ASInv L y.
Proof.
  intros I Sch L x y HI AI P Q E; unfold at_boundary in E; rewrite P in E.
  assert (Hsub : forall s, sub x = Some s -> at_boundary_sub I Sch x s = Some y -> ASInv L y).
  { intros s S0 Eb; unfold at_boundary_sub in Eb.
    destruct (arrived Sch (micro x) <=? cursor x)%nat; [discriminate |].
    destruct (nth_error (entries I) (cursor x)) as [[c r |] |]; [| | discriminate].
    - destruct (Nat.eqb c (sub_cmd s)).
      + inversion Eb; subst; apply step_sinv_on_notify; fields; auto;
          [apply step_inv_set_cursor; auto | apply (step_ainv_same L x); auto].
      + destruct (c <? next_cmd x)%nat; inversion Eb; subst; intros _.
        apply (step_ainv_same L x); auto.
    - inversion Eb; subst; apply step_sinv_on_cancel; fields; auto;
        [apply step_inv_set_cursor; auto | apply (step_ainv_same L x); auto]. }
  destruct (held x) eqn:H, (waiter x) as [[[f tok] op] |] eqn:W.
  - inversion E; subst; intros _.
    assert (Ha : awaiter x = Some (f, tok)) by exact (a_waiter _ _ AI f tok op W).
    assert (Hs : not_sop (sub x) /\ follows_pair (sub x) = None).
    { destruct (a_slot _ _ AI) as [S0 | S0]; [congruence | rewrite S0; cbn; auto |].
      split; [apply step_slot_not_sop | apply step_slot_follows]; auto. }
    destruct Hs as [Hs1 Hs2].
    constructor; fields; rewrite ?Q; try discriminate.
    + intros c f' tok' op' k rest S0; rewrite S0 in Hs1; contradiction.
    + intros f' tok' H'; rewrite Hs2 in H'; discriminate.
    + intros H'; exfalso; apply H'; reflexivity.
    + exact (a_tok _ _ AI).
    + intros t f' tok' [Ht | []] Hd; subst t; inversion Hd; subst.
      split; [exact (a_tok _ _ AI f' tok' Ha) | auto].
  - destruct (sub x) as [s |] eqn:S0; [eapply Hsub; eauto |].
    inversion E; subst; intros Py; rewrite (step_violate_stays _ _ Py); auto.
  - destruct (sub x) as [s |] eqn:S0; [eapply Hsub; eauto |].
    inversion E; subst; intros Py.
    destruct (step_issue_op_stays _ _ _ _ _ Py) as (H1 & H2 & H3 & _ & c & op' & k & rest
      & H4).
    assert (Ha : awaiter x = Some (f, tok)) by exact (a_waiter _ _ AI f tok op W).
    constructor; rewrite ?H1, ?H2, ?H3, ?H4; fields; rewrite ?Q; try discriminate.
    + intros c' f' tok' op'' k' r' E'; inversion E'; subst; auto.
    + intros H'; exfalso; apply H'; reflexivity.
    + exact (a_tok _ _ AI).
    + intros t f' tok' [].
  - destruct (sub x) as [s |] eqn:S0; [eapply Hsub; eauto |].
    inversion E; subst; intros Py; rewrite (step_violate_stays _ _ Py); auto.
Qed.

(** ** Held cancellations at a turn boundary *)

Lemma step_hinv_short : forall z, (held z = true -> init_or_none (sub z)) ->
  (forall f tok, ~ In (DeliverCancel f tok) (queue z)) -> HInv z.
Proof. intros; apply step_hinv_nodc; auto. Qed.

Lemma step_not_init_held : forall x, HInv x -> (init_or_none (sub x) -> False) ->
  held x = false.
Proof.
  intros x HH N; destruct (held x) eqn:H; auto; exfalso; exact (N (h_held _ HH H)).
Qed.

Lemma step_hinv_after_sample : forall I L x y after, AInv L x -> HInv x -> queue x = [] ->
  (exists c, sub x = Some (SSample c after)) ->
  sub y = None -> awaiter y = awaiter x -> held y = held x -> queue y = queue x ->
  phase y = POpen -> phase (after_sample I y after) = POpen ->
  HInv (after_sample I y after).
Proof.
  intros I L x y after AI HH Q [c S0] Hs Ha Hh Hq P Py.
  assert (Hnone : init_or_none (sub y)) by (left; auto).
  destruct after as [| f tok o | f tok k rest | f tok | f tok k]; cbn [after_sample] in *.
  - apply step_hinv_short; fields; [intros; exact Hnone |].
    rewrite Hq, Q; cbn; intros g tk [E | []]; discriminate.
  - apply step_hinv_short; fields; [intros; exact Hnone |].
    rewrite Hq, Q; cbn; intros g tk [E | []]; discriminate.
  - destruct (link_of rest) as [[chunk rest'] |].
    + destruct (step_issue_stays _ _ _ _ _ Py) as (H1 & H2 & H3 & H4 & _).
      apply step_hinv_short; rewrite ?H3, ?H4, ?Hq, ?Q; auto.
      intros H; rewrite Hh in H.
      rewrite (step_not_init_held x HH) in H; [discriminate |].
      rewrite S0; intros [E | [c' E]]; discriminate.
    + apply step_hinv_short; fields; [intros; exact Hnone |].
      rewrite Hq, Q; cbn; intros g tk [E | []]; discriminate.
  - constructor; fields; [intros; exact Hnone |].
    rewrite Hq, Q; cbn; intros g tk [E | []]; inversion E; subst.
    split; [rewrite Ha; apply (a_sample _ _ AI); rewrite S0; reflexivity |].
    split; [exact Hnone |]; unfold cnt; cbn; rewrite step_pair_eqb_refl; reflexivity.
  - apply step_hinv_short; fields; [intros; exact Hnone |].
    rewrite Hq, Q; cbn; intros g tk [].
Qed.

Lemma step_hinv_on_notify : forall I L x s r, Inv x -> AInv L x -> HInv x ->
  phase x = POpen -> queue x = [] -> sub x = Some s ->
  phase (on_notify I x s r) = POpen -> HInv (on_notify I x s r).
Proof.
  intros I L x s r HI AI HH P Q S0 Py.
  assert (Hv : violated x = false).
  { destruct (violated x) eqn:V; auto; exfalso; exact (inv_viol _ HI V P). }
  assert (Hnq : forall f tok, ~ In (DeliverCancel f tok) (queue x)) by (rewrite Q; auto).
  destruct s as [c f tok op k rest | c after | c]; unfold on_notify in *.
  - assert (Hf : held x = false)
      by (apply (step_not_init_held x HH); rewrite S0; intros [E | [c' E]]; discriminate).
    destruct op as [kk aa | d], r as [o | v |]; auto; unfold issue_sample in *;
      destruct (step_issue_stays _ _ _ _ _ Py) as (H1 & H2 & H3 & H4 & _);
      apply step_hinv_short; rewrite ?H3, ?H4, ?Hf; auto; intros Hx; discriminate.
  - destruct r as [o | v |].
    + destruct after; auto; apply step_hinv_short; fields; auto; intros; left; auto.
    + destruct after as [| f tok o | f tok kk rest | f tok | f tok kk];
        [| | | | apply step_hinv_short; fields; auto; intros; left; auto];
      (cbv zeta in *; match goal with H : context [apply_sample ?x ?c ?v ?a] |- _ =>
        destruct (step_apply_sample_cases x c v a) as [E | (a' & l & Ha' & E)]; rewrite E in *;
        [destruct (step_violate_open x Overflow P Hv) as [Hp _]; rewrite Hp in Py;
         cbv iota in Py; rewrite Hp in Py; discriminate |]
       end);
      fields; rewrite P in *;
      (apply (step_hinv_after_sample I L x); fields; eauto).
    + destruct after; try (apply step_hinv_short; fields; auto; intros; left; auto; fail);
        rewrite (step_violate_stays _ _ Py); auto.
  - apply step_hinv_short; fields; auto; intros; left; auto.
Qed.

Lemma step_hinv_on_cancel : forall I x s, Inv x -> HInv x -> phase x = POpen ->
  queue x = [] -> sub x = Some s -> phase (on_cancel I x s) = POpen ->
  HInv (on_cancel I x s).
Proof.
  intros I x s HI HH P Q S0 Py.
  assert (Hnq : forall f tok, ~ In (DeliverCancel f tok) (queue x)) by (rewrite Q; auto).
  assert (Hf : (init_or_none (sub x) -> False) -> held x = false)
    by (apply step_not_init_held; auto).
  destruct s as [c f tok op k rest | c after | c]; cbn [on_cancel] in *.
  - destruct (step_issue_sample_stays _ _ _ Py) as (H1 & H2 & H3 & _ & c' & H4).
    apply step_hinv_short; rewrite ?H3; auto.
    unfold issue_sample in *; destruct (step_issue_stays _ _ _ _ _ Py) as (_ & _ & _ & H5 & _).
    rewrite H5, Hf; [discriminate |]; rewrite S0; intros [E | [? E]]; discriminate.
  - destruct after as [| f tok o | f tok kk rest | f tok | f tok kk];
      try (apply step_hinv_short; fields; auto; intros; left; auto; fail);
      destruct (step_issue_sample_stays _ _ _ Py) as (H1 & H2 & H3 & _ & c' & H4);
      apply step_hinv_short; rewrite ?H3, ?H4; fields; auto;
      try (intros; right; eauto; fail);
      unfold issue_sample in *; destruct (step_issue_stays _ _ _ _ _ Py) as (_ & _ & _ & H5 & _);
      rewrite H5, Hf; try discriminate; rewrite S0; intros [E | [? E]]; discriminate.
  - apply step_hinv_short; fields; auto; intros; left; auto.
Qed.

Lemma step_hinv_boundary : forall I Sch L x y, Inv x -> AInv L x -> HInv x ->
  phase x = POpen -> queue x = [] -> at_boundary I Sch x = Some y -> phase y = POpen ->
  HInv y.
Proof.
  intros I Sch L x y HI AI HH P Q E Py; unfold at_boundary in E; rewrite P in E.
  assert (Hsub : forall s, sub x = Some s -> at_boundary_sub I Sch x s = Some y -> HInv y).
  { intros s S0 Eb; unfold at_boundary_sub in Eb.
    destruct (arrived Sch (micro x) <=? cursor x)%nat; [discriminate |].
    destruct (nth_error (entries I) (cursor x)) as [[c r |] |]; [| | discriminate].
    - destruct (Nat.eqb c (sub_cmd s)).
      + inversion Eb; subst; apply (step_hinv_on_notify I L); fields; auto;
          [apply step_inv_set_cursor; auto | apply (step_ainv_same L x); auto |
           apply (step_hinv_same x); auto].
      + destruct (c <? next_cmd x)%nat; inversion Eb; subst.
        apply (step_hinv_same x); auto.
    - inversion Eb; subst; apply step_hinv_on_cancel; fields; auto;
        [apply step_inv_set_cursor; auto | apply (step_hinv_same x); auto]. }
  destruct (held x) eqn:H, (waiter x) as [[[f tok] op] |] eqn:W.
  - inversion E; subst; constructor; fields; [discriminate |].
    rewrite Q; intros g tk [E' | []]; inversion E'; subst.
    split; [exact (a_waiter _ _ AI g tk op W) |].
    split; [exact (h_held _ HH H) |]; unfold cnt; cbn; rewrite step_pair_eqb_refl; auto.
  - destruct (sub x) as [s |] eqn:S0; [eapply Hsub; eauto |].
    inversion E; subst; rewrite (step_violate_stays _ _ Py); auto.
  - destruct (sub x) as [s |] eqn:S0; [eapply Hsub; eauto |].
    inversion E; subst.
    destruct (step_issue_op_stays _ _ _ _ _ Py) as (H1 & H2 & H3 & _).
    apply step_hinv_short; rewrite ?H3, ?step_issue_op_held; fields; rewrite ?H, ?Q;
      auto; discriminate.
  - destruct (sub x) as [s |] eqn:S0; [eapply Hsub; eauto |].
    inversion E; subst; rewrite (step_violate_stays _ _ Py); auto.
Qed.

Lemma step_sinv_boundary : forall I Sch L x y, Inv x -> phase x = POpen ->
  queue x = [] -> SInv L x -> at_boundary I Sch x = Some y -> SInv L y.
Proof.
  intros I Sch L x y HI P Q SI E Py; destruct (SI P) as [AI HH]; split;
    [eapply step_asinv_boundary | eapply step_hinv_boundary]; eauto.
Qed.

(** ** One step, and a run *)

Lemma step_sinv_set_micro : forall L y v, SInv L y -> SInv L (set_micro y v).
Proof. intros L y v H; apply (step_sinv_same L y); auto. Qed.

Lemma step_sinv_set_progress : forall L y v, SInv L y -> SInv L (set_progress y v).
Proof. intros L y v H; apply (step_sinv_same L y); auto. Qed.

Lemma step_sinv_step : forall R I Sch s L, Inv (xs s) -> SInv L (xs s) ->
  NoDup (start_tokens (L ++ fst (step_log R I Sch s))) ->
  SInv (L ++ fst (step_log R I Sch s)) (xs (step R I Sch s)).
Proof.
  intros R I Sch s L HI SI Hnd.
  destruct (phase (xs s)) eqn:P.
  2,3: intros Py; exfalso; revert Py; apply step_closed_step; congruence.
  unfold step_log in *; rewrite step_xs; rewrite P in *.
  destruct (stop_due Sch (xs s)); [intros Py; fields; discriminate |].
  destruct (foreign_due I (xs s)) as [fi |].
  { cbn [fst]; rewrite app_nil_r; apply step_sinv_set_micro; intros Py.
    destruct fi; cbn [on_foreign] in *; try rewrite (step_violate_stays _ _ Py);
      apply (step_sinv_same L (xs s)); auto. }
  destruct (cut_due Sch (xs s)) as [k |].
  { intros Py; fields; unfold on_cut in Py; exfalso.
    destruct k; try (rewrite step_close_open in Py; [discriminate | fields; auto]).
    fields; discriminate. }
  destruct (queue (xs s)) as [| t rest] eqn:Q.
  - cbn [fst]; rewrite app_nil_r; destruct (at_boundary I Sch (xs s)) as [y |] eqn:E.
    + apply step_sinv_set_micro, step_sinv_set_progress.
      eapply step_sinv_boundary; eauto.
    + apply step_sinv_set_micro; auto.
  - apply step_sinv_set_micro; rewrite step_run_head_eq; cbn [fst] in *.
    replace (L ++ LTask t :: ilog I (head_state (xs s) t rest) (run_task R (rs s) t))
      with ((L ++ [LTask t]) ++ ilog I (head_state (xs s) t rest) (run_task R (rs s) t))
      in * by (rewrite <- app_assoc; reflexivity).
    apply step_sinv_interp; auto.
    + apply step_head_state_iinv; auto.
    + apply step_sinv_head; auto.
Qed.

Lemma step_elog_fst : forall R I Sch n s,
  fst (elog R I Sch (S n) s) =
  fst (step_log R I Sch s) ++ fst (elog R I Sch n (step R I Sch s)).
Proof.
  intros; cbn [elog]; destruct (step_log R I Sch s); destruct (elog R I Sch n _); reflexivity.
Qed.

Lemma step_sinv_iterate : forall R I Sch n s L, Inv (xs s) -> SInv L (xs s) ->
  NoDup (start_tokens (L ++ fst (elog R I Sch n s))) ->
  SInv (L ++ fst (elog R I Sch n s)) (xs (iterate R I Sch n s)).
Proof.
  intros R I Sch n; induction n as [| n IH]; intros s L HI SI Hnd.
  - cbn; rewrite app_nil_r; exact SI.
  - rewrite step_elog_fst, app_assoc in *; cbn [iterate].
    apply IH; auto.
    + apply step_inv_step; auto.
    + apply step_sinv_step; auto.
      rewrite step_start_tokens_app in Hnd; apply NoDup_app_remove_r in Hnd; exact Hnd.
Qed.

Lemma step_sinv_initial : forall R p I, SInv [] (xs (initial R p I)).
Proof.
  intros R p I Py; cbn [initial xs] in *.
  destruct (step_issue_sample_stays _ _ _ Py) as (H1 & H2 & H3 & _ & c & H4).
  split; constructor; rewrite ?H1, ?H2, ?H3, ?H4; cbn; try discriminate; try tauto.
  unfold issue_sample in *; destruct (step_issue_stays _ _ _ _ _ Py) as (_ & _ & _ & H5 & _).
  rewrite H5; cbn; discriminate.
Qed.

(** ** S4 *)

Theorem step_s4 : S4.
Proof.
  split.
  - intros R HM p I Sch s [n ->] P.
    destruct HM as [_ [[_ Hnd] _]].
    set (Lg := elog R I Sch n (initial R p I)).
    specialize (Hnd p (seed I) (answers_of (fst Lg)) (snd Lg)).
    pose proof (step_open_log_is_drive R I Sch n (initial R p I) P) as Hd; cbv zeta in Hd.
    change (rs (initial R p I)) with (init R p (seed I)) in Hd; fold Lg in Hd.
    rewrite Hd in Hnd.
    pose proof (step_sinv_iterate R I Sch n (initial R p I) [] (step_inv_initial R p I)
                  (step_sinv_initial R p I) Hnd) as SI.
    destruct (SI P) as [[A B C D E F] _]; split; eauto.
  - intros I x f tok op P V Ha Z; unfold on_start; rewrite P; cbv zeta; rewrite Z.
    fields; destruct (awaiter x) as [a |]; [| congruence].
    assert (Hv : violated (emit x (AStart f tok op)) = false) by (fields; auto).
    assert (Hp : phase (emit x (AStart f tok op)) = POpen) by (fields; auto).
    destruct (step_violate_open _ SecondOp Hp Hv) as [H1 H2].
    rewrite H1, H2; fields; rewrite <- app_assoc; split; [reflexivity | discriminate].
Qed.
