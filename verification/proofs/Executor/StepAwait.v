(** * Step domain: the one awaiter (S4's first clause).

    [AInv L x] relates the awaiter, the waiter, the subscription and the queued deliveries of
    an open state [x] to the log [L] the runtime has reported so far. The only fact it takes
    from the runtime is I4's second half: no token is started twice in a log. With it, a
    queued delivery can never be for a token that a later start reuses, so a delivery that
    clears the awaiter never leaves a subscribed operation or a waiter without one. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Statements StepInv StepTurn StepLog.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

Definition dpair (t : Task) : option (FiberId * Token) :=
  match t with Deliver f tok _ | DeliverCancel f tok => Some (f, tok) | _ => None end.

Definition not_sop (s : option Sub) : Prop :=
  match s with Some (SOp _ _ _ _ _ _) => False | _ => True end.

(** The fiber a sample is issued for, when it is one the fiber still waits on. *)
Definition follows_pair (s : option Sub) : option (FiberId * Token) :=
  match s with
  | Some (SSample _ (FResult f tok _)) | Some (SSample _ (FLink f tok _ _))
  | Some (SSample _ (FCancelled f tok)) => Some (f, tok)
  | _ => None
  end.

Record AInv (L : list LogEntry) (x : XState) : Prop := {
  a_waiter : forall f tok op, waiter x = Some (f, tok, op) -> awaiter x = Some (f, tok);
  a_sop : forall c f tok op k rest, sub x = Some (SOp c f tok op k rest) ->
          awaiter x = Some (f, tok);
  a_sample : forall f tok, follows_pair (sub x) = Some (f, tok) -> awaiter x = Some (f, tok);
  a_slot : waiter x <> None -> sub x = None \/ slot_held x = true;
  a_tok : forall f tok, awaiter x = Some (f, tok) -> In tok (start_tokens L);
  a_queue : forall t f tok, In t (queue x) -> dpair t = Some (f, tok) ->
            In tok (start_tokens L) /\
            (awaiter x = Some (f, tok) -> waiter x = None /\ not_sop (sub x))
}.

Definition SInv (L : list LogEntry) (x : XState) : Prop := phase x = POpen -> AInv L x.

(** ** Basic facts *)

Lemma step_pair_eqb_true : forall a b, pair_eqb a b = true -> a = b.
Proof.
  intros [a1 a2] [b1 b2] H; unfold pair_eqb in H; cbn in H.
  apply andb_true_iff in H; destruct H as [H1 H2].
  apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2; subst; reflexivity.
Qed.

Lemma step_pair_eqb_refl : forall a, pair_eqb a a = true.
Proof. intros [a1 a2]; unfold pair_eqb; cbn; rewrite !Nat.eqb_refl; reflexivity. Qed.

Lemma step_start_tokens_app : forall L1 L2,
  start_tokens (L1 ++ L2) = start_tokens L1 ++ start_tokens L2.
Proof. intros; unfold start_tokens; apply flat_map_app. Qed.

Lemma step_nodup_new : forall L f tok op,
  NoDup (start_tokens (L ++ [LEvent (EvStart f tok op)])) -> ~ In tok (start_tokens L).
Proof.
  intros L f tok op H; rewrite step_start_tokens_app in H; cbn in H.
  apply NoDup_remove_2 in H; rewrite app_nil_r in H; exact H.
Qed.

Lemma step_follows_active : forall s p, follows_pair s = Some p -> active s = true.
Proof.
  intros [[c f tok op k rest | c [| f tok o | f tok k rest | f tok | f tok k] | c] |] p H;
    try discriminate; reflexivity.
Qed.

Lemma step_slot_not_sop : forall x, slot_held x = true -> not_sop (sub x).
Proof.
  intros x H; unfold slot_held in H; destruct (sub x) as [[] |]; cbn; auto; discriminate.
Qed.

Lemma step_slot_follows : forall x, slot_held x = true -> follows_pair (sub x) = None.
Proof.
  intros x H; unfold slot_held in H;
    destruct (sub x) as [[c f tok op k rest | c [] | c] |]; cbn; auto; discriminate.
Qed.

Lemma step_ainv_same : forall L x y, AInv L x ->
  awaiter y = awaiter x -> waiter y = waiter x -> sub y = sub x ->
  (forall t, In t (queue y) -> In t (queue x) \/ dpair t = None) -> AInv L y.
Proof.
  intros L x y [A B C D E F] Ha Hw Hs Hq.
  assert (Hsl : slot_held y = slot_held x) by (unfold slot_held; rewrite Hs; reflexivity).
  constructor; rewrite ?Ha, ?Hw, ?Hs, ?Hsl; auto.
  intros t f tok Ht Hd; destruct (Hq t Ht) as [Ht1 | Hn];
    [exact (F t f tok Ht1 Hd) | congruence].
Qed.

Lemma step_ainv_mono : forall L L' x, AInv L x ->
  (forall t, In t (start_tokens L) -> In t (start_tokens L')) -> AInv L' x.
Proof.
  intros L L' x [A B C D E F] M; constructor; auto.
  - intros f tok H; apply M, (E f tok H).
  - intros t f tok H1 H2; destruct (F t f tok H1 H2); auto.
Qed.

Lemma step_mono_app : forall L L2 t, In t (start_tokens L) -> In t (start_tokens (L ++ L2)).
Proof. intros; rewrite step_start_tokens_app; apply in_or_app; auto. Qed.

(** A state with no awaiter, no waiter and no operation or awaited sample subscribed. *)
Lemma step_ainv_cleared : forall L x y, AInv L x ->
  awaiter y = None -> waiter y = None -> not_sop (sub y) -> follows_pair (sub y) = None ->
  (forall t, In t (queue y) -> In t (queue x)) -> AInv L y.
Proof.
  intros L x y [A B C D E F] Ha Hw Hs Hf Hq; constructor; rewrite ?Ha, ?Hw; try congruence.
  - intros c f tok op k rest S0; rewrite S0 in Hs; contradiction.
  - intros t f tok H1 H2; split; [apply (F t f tok); auto | discriminate].
Qed.

(** ** Operations that leave an open state *)

Lemma step_violate_stays : forall x v, phase (violate x v) = POpen -> violate x v = x.
Proof.
  intros x v P; unfold violate in *; destruct (violated x); auto.
  exfalso; destruct (phase x) eqn:E.
  - rewrite step_close_open in P; [discriminate | fields; auto].
  - revert P; apply step_close_phase; fields; congruence.
  - revert P; apply step_close_phase; fields; congruence.
Qed.

Lemma step_close_stays : forall x c, phase (close x c) = POpen -> close x c = x.
Proof.
  intros x c P; destruct (phase x) eqn:E.
  - rewrite step_close_open in P; [discriminate | auto].
  - exfalso; revert P; apply step_close_phase; congruence.
  - exfalso; revert P; apply step_close_phase; congruence.
Qed.

Lemma step_issue_stays : forall I x k o s, phase (issue I x k o s) = POpen ->
  awaiter (issue I x k o s) = awaiter x /\ waiter (issue I x k o s) = waiter x /\
  queue (issue I x k o s) = queue x /\ held (issue I x k o s) = held x /\
  phase x = POpen /\ sub (issue I x k o s) = Some (s (next_cmd x)).
Proof.
  intros I x k o s; unfold issue; cbv zeta.
  destruct (nth_error (persisted I) (next_cmd x)); [destruct (cmd_eqb k c) |];
    fields; intros P; try discriminate; repeat split; auto.
Qed.

Lemma step_issue_op_stays : forall I x f tok op, phase (issue_op I x f tok op) = POpen ->
  awaiter (issue_op I x f tok op) = awaiter x /\ waiter (issue_op I x f tok op) = waiter x /\
  queue (issue_op I x f tok op) = queue x /\ phase x = POpen /\
  exists c op' k rest, sub (issue_op I x f tok op) = Some (SOp c f tok op' k rest).
Proof.
  intros I x f tok op; unfold issue_op; destruct op as [kk a | d];
    [| destruct (match d with Millis m => split m | Forever => (max_chunk, Endless) end)];
    intros P; destruct (step_issue_stays _ _ _ _ _ P) as (H1 & H2 & H3 & _ & H5 & H6);
    repeat split; auto; rewrite H6; eauto.
Qed.

Lemma step_issue_sample_stays : forall I x a, phase (issue_sample I x a) = POpen ->
  awaiter (issue_sample I x a) = awaiter x /\ waiter (issue_sample I x a) = waiter x /\
  queue (issue_sample I x a) = queue x /\ phase x = POpen /\
  exists c, sub (issue_sample I x a) = Some (SSample c a).
Proof.
  intros I x a P; unfold issue_sample in *;
    destruct (step_issue_stays _ _ _ _ _ P) as (H1 & H2 & H3 & _ & H5 & H6);
    repeat split; auto; rewrite H6; eauto.
Qed.

(** ** Events *)

Lemma step_ainv_start : forall I x f tok op L, IInv x -> phase x = POpen -> AInv L x ->
  NoDup (start_tokens (L ++ [LEvent (EvStart f tok op)])) ->
  SInv (L ++ [LEvent (EvStart f tok op)]) (on_start I x f tok op).
Proof.
  intros I x f tok op L [HI HA] P AI Hnd Py.
  set (L' := L ++ [LEvent (EvStart f tok op)]) in *.
  pose proof (step_nodup_new _ _ _ _ Hnd) as Hn.
  assert (Hin : In tok (start_tokens L')).
  { unfold L'; rewrite step_start_tokens_app; apply in_or_app; right; left; reflexivity. }
  assert (AI' : AInv L' x) by (apply (step_ainv_mono L); auto; intros; apply step_mono_app; auto).
  (* No queued delivery is for the new token. *)
  assert (Hq : forall t f' tok', In t (queue x) -> dpair t = Some (f', tok') -> tok' <> tok).
  { intros t f' tok' Ht Hd E; subst; apply Hn; exact (proj1 (a_queue _ _ AI t f' tok Ht Hd)). }
  unfold on_start in *; rewrite P in *; cbv zeta in *.
  set (y := emit x (AStart f tok op)) in *.
  assert (AY : AInv L' y) by (apply (step_ainv_same _ x); auto).
  subst y; fields.
  destruct (zero_sleep op).
  - (* A zero sleep queues its delivery at once. *)
    destruct AY as [A B C D E F]; constructor; fields; auto.
    intros t f' tok' Ht Hd; apply in_app_or in Ht; destruct Ht as [Ht | [Ht | []]]; eauto.
    subst; inversion Hd; subst; split; auto.
    intros Ha; exfalso; apply Hn; exact (a_tok _ _ AI f' tok' Ha).
  - destruct (awaiter x) as [a |] eqn:Ea.
    + rewrite (step_violate_stays _ _ Py); auto.
    + assert (Hw : waiter x = None).
      { destruct (waiter x) as [[[g tk] o] |] eqn:W; auto.
        pose proof (a_waiter _ _ AI g tk o W); congruence. }
      assert (Hnew : forall t f' tok', In t (queue x) -> dpair t = Some (f', tok') ->
                Some (f, tok) = Some (f', tok') -> False).
      { intros t f' tok' Ht Hd E; inversion E; subst; exact (Hq t f' tok' Ht Hd eq_refl). }
      destruct (held x) eqn:Hh.
      * (* A held cancellation is delivered to the new awaiter. *)
        assert (Hs : not_sop (sub x) /\ follows_pair (sub x) = None).
        { destruct (inv_held _ HI Hh) as [S0 | [c S0]]; rewrite S0; cbn; auto. }
        destruct Hs as [Hs1 Hs2].
        constructor; fields; rewrite ?Hw.
        -- intros f' tok' op' H; discriminate.
        -- intros c f' tok' op' k rest S0; rewrite S0 in Hs1; contradiction.
        -- intros f' tok' H; rewrite Hs2 in H; discriminate.
        -- intros H; exfalso; apply H; reflexivity.
        -- intros f' tok' H; inversion H; subst; auto.
        -- intros t f' tok' Ht Hd; apply in_app_or in Ht; destruct Ht as [Ht | [Ht | []]].
           ++ split; [exact (proj1 (a_queue _ _ AI' t f' tok' Ht Hd)) |].
              intros E; exfalso; eauto.
           ++ subst; inversion Hd; subst; split; auto.
      * destruct (slot_held _) eqn:Hsl.
        -- (* The slot is held: the fiber waits for it. *)
           constructor; fields.
           ++ intros f' tok' op' H; inversion H; subst; auto.
           ++ intros c f' tok' op' k rest S0.
              pose proof (step_slot_not_sop _ Hsl) as N; fields; rewrite S0 in N; contradiction.
           ++ intros f' tok' H; pose proof (step_slot_follows _ Hsl) as N; fields;
                congruence.
           ++ intros _; right; exact Hsl.
           ++ intros f' tok' H; inversion H; subst; auto.
           ++ intros t f' tok' Ht Hd.
              split; [exact (proj1 (a_queue _ _ AI' t f' tok' Ht Hd)) |].
              intros E; exfalso; eauto.
        -- (* The slot is free: the command is issued. *)
           destruct (step_issue_op_stays _ _ _ _ _ Py) as (H1 & H2 & H3 & _ & c & op' & k &
             rest & H4).
           constructor; rewrite ?H1, ?H2, ?H3, ?H4; fields; rewrite ?Hw.
           ++ intros f' tok' op'' H; discriminate.
           ++ intros c' f' tok' op'' k' rest' E; inversion E; subst; auto.
           ++ intros f' tok' H; discriminate.
           ++ intros H; exfalso; apply H; reflexivity.
           ++ intros f' tok' H; inversion H; subst; auto.
           ++ intros t f' tok' Ht Hd.
              split; [exact (proj1 (a_queue _ _ AI' t f' tok' Ht Hd)) |].
              intros E; exfalso; eauto.
Qed.

Lemma step_release_sub_sop : forall c f tok op k rest,
  release_sub (SOp c f tok op k rest) = Some (f, tok, SReleased c).
Proof. reflexivity. Qed.

Lemma step_ainv_release : forall x f tok L, IInv x -> phase x = POpen -> AInv L x ->
  AInv L (on_release x f tok).
Proof.
  intros x f tok L [HI HA] P AI; unfold on_release; cbv zeta; rewrite P.
  set (y := set_queue x (filter (fun t => negb (for_token f tok t)) (queue x))).
  assert (Hq : forall t, In t (queue y) -> In t (queue x)).
  { intros t Ht; unfold y in Ht; fields; apply filter_In in Ht; tauto. }
  assert (AY : AInv L y) by (apply (step_ainv_same _ x); auto).
  assert (Hf : follows_pair (sub x) = None).
  { destruct (follows_pair (sub x)) eqn:E; auto.
    apply step_follows_active in E; congruence. }
  subst y; fields; rewrite P.
  destruct (awaiter x) as [a |] eqn:Ea; [| exact AY].
  destruct (negb (pair_eqb a (f, tok))) eqn:Ep; [exact AY |].
  apply negb_false_iff, step_pair_eqb_true in Ep; subst a.
  destruct (waiter x) as [w |] eqn:W.
  - apply (step_ainv_cleared _ _ _ AY); fields; auto.
    destruct (a_slot _ _ AI) as [S0 | S0]; [congruence | | apply step_slot_not_sop; auto].
    rewrite S0; cbn; auto.
  - destruct (sub x) as [s |] eqn:S0.
    + destruct (release_sub s) as [[[f' tok'] s'] |] eqn:R.
      * destruct (step_release_sub_cases s f' tok' s' R) as (c & f0 & tok0 & op & k & rest &
          E1 & E2); [exact HA |]; subst s s'.
        rewrite step_release_sub_sop in R; inversion R; subst f' tok'.
        pose proof (a_sop _ _ AI c f0 tok0 op k rest S0) as Ha; rewrite Ea in Ha.
        inversion Ha; subst f0 tok0; rewrite step_pair_eqb_refl.
        apply (step_ainv_cleared _ _ _ AY); fields; cbn; auto.
      * apply (step_ainv_cleared _ _ _ AY); fields; rewrite ?S0; auto.
        destruct s; cbn; auto; discriminate.
    + apply (step_ainv_cleared _ _ _ AY); fields; rewrite ?S0; cbn; auto.
Qed.

Lemma step_sinv_event : forall I x e L, IInv x -> SInv L x ->
  NoDup (start_tokens (L ++ [LEvent e])) -> SInv (L ++ [LEvent e]) (on_event I x e).
Proof.
  intros I x e L HI SI Hnd Py.
  destruct (phase x) eqn:P.
  2,3: exfalso; revert Py; apply step_on_event_closed; congruence.
  pose proof (SI P) as AI.
  assert (AI' : AInv (L ++ [LEvent e]) x)
    by (apply (step_ainv_mono L); auto; intros; apply step_mono_app; auto).
  unfold on_event in *; rewrite P in *.
  destruct e as [f tok op | f tok | pr t | f | r].
  - apply step_ainv_start; auto.
  - apply step_ainv_release; auto.
  - destruct (Nat.eqb pr 0).
    + apply (step_ainv_same _ x); auto; fields; intros t' Ht.
      apply in_app_or in Ht; destruct Ht as [Ht | [Ht | []]]; auto; subst; auto.
    + rewrite (step_violate_stays _ _ Py); auto.
  - apply (step_ainv_same _ x); auto.
  - destruct (root_exit x).
    + rewrite (step_violate_stays _ _ Py); auto.
    + rewrite (step_close_stays _ _ Py); apply (step_ainv_same _ x); auto.
Qed.

(** ** Inside a task *)

Lemma step_sinv_mono : forall L L' x, SInv L x ->
  (forall t, In t (start_tokens L) -> In t (start_tokens L')) -> SInv L' x.
Proof. intros L L' x H M P; apply (step_ainv_mono L); auto. Qed.

Lemma step_sinv_same : forall L x y, SInv L x -> phase y = phase x ->
  awaiter y = awaiter x -> waiter y = waiter x -> sub y = sub x ->
  queue y = queue x -> SInv L y.
Proof.
  intros L x y H P Ha Hw Hs Hq Py; apply (step_ainv_same L x); auto.
  - apply H; congruence.
  - intros t Ht; rewrite Hq in Ht; auto.
Qed.

Lemma step_sinv_interp : forall {X} I (s : Script X) x L, IInv x -> SInv L x ->
  NoDup (start_tokens (L ++ ilog I x s)) -> SInv (L ++ ilog I x s) (fst (interp I x s)).
Proof.
  intros X I s; induction s as [r | e k IH | f k IH | f k IH | f k IH];
    intros x L HI SI Hnd; cbn [ilog interp fst] in *.
  - rewrite app_nil_r; exact SI.
  - replace (L ++ LEvent e :: ilog I (on_event I x e) k)
      with ((L ++ [LEvent e]) ++ ilog I (on_event I x e) k) in *
      by (rewrite <- app_assoc; reflexivity).
    apply IH; auto using step_on_event_iinv.
    apply step_sinv_event; auto.
    rewrite step_start_tokens_app in Hnd; apply NoDup_app_remove_r in Hnd; exact Hnd.
  - set (y := match phase x with PDone => x | _ => emit x (AClock f (logical x)) end) in *.
    replace (L ++ LClock f (logical x) :: ilog I y (k (logical x)))
      with ((L ++ [LClock f (logical x)]) ++ ilog I y (k (logical x))) in *
      by (rewrite <- app_assoc; reflexivity).
    apply IH; [| | exact Hnd].
    + unfold y; destruct (phase x); auto; apply step_iinv_emit; auto.
    + apply (step_sinv_mono L); [| intros; apply step_mono_app; auto].
      unfold y; destruct (phase x) eqn:P; auto;
        apply (step_sinv_same _ x); fields; auto.
  - set (y := match phase x with
              | PDone => x
              | _ => emit (set_draws x (S (draws x))) (ADraw f (stream I (draws x))) end) in *.
    replace (L ++ LDraw f (stream I (draws x)) :: ilog I y (k (stream I (draws x))))
      with ((L ++ [LDraw f (stream I (draws x))]) ++ ilog I y (k (stream I (draws x)))) in *
      by (rewrite <- app_assoc; reflexivity).
    apply IH; [| | exact Hnd].
    + unfold y; destruct (phase x); auto; apply step_iinv_emit; auto;
        apply step_iinv_set_draws; auto.
    + apply (step_sinv_mono L); [| intros; apply step_mono_app; auto].
      unfold y; destruct (phase x) eqn:P; auto;
        apply (step_sinv_same _ x); fields; auto.
  - set (b := match phase x with PClosing _ => true | _ => false end) in *.
    set (y := match phase x with PDone => x | _ => emit x (ARegister f) end) in *.
    replace (L ++ LRegister f b :: ilog I (set_live y (live y ++ [f])) (k b))
      with ((L ++ [LRegister f b]) ++ ilog I (set_live y (live y ++ [f])) (k b)) in *
      by (rewrite <- app_assoc; reflexivity).
    assert (HY : IInv y) by (unfold y; destruct (phase x); auto; apply step_iinv_emit; auto).
    assert (SY : SInv L y)
      by (unfold y; destruct (phase x) eqn:P; auto; apply (step_sinv_same _ x); fields; auto).
    apply IH; [| | exact Hnd].
    + destruct HY as [H1 H2]; split; [apply step_inv_set_live |]; auto.
    + apply (step_sinv_mono L); [| intros; apply step_mono_app; auto].
      apply (step_sinv_same _ y); fields; auto.
Qed.

Lemma step_ainv_head : forall x t rest L, Inv x -> phase x = POpen ->
  queue x = t :: rest -> AInv L x -> AInv (L ++ [LTask t]) (head_state x t rest).
Proof.
  intros x t rest L HI P Q AI.
  apply (step_ainv_mono L); [| intros; apply step_mono_app; auto].
  assert (Hf : follows_pair (sub x) = None).
  { destruct (follows_pair (sub x)) eqn:E; auto.
    apply step_follows_active, (inv_active _ HI) in E; congruence. }
  assert (Hsub : forall u, In u rest -> In u (queue x)) by (intros; rewrite Q; right; auto).
  unfold head_state; cbv zeta.
  set (y0 := set_progress (set_queue x rest) (S (progress x))).
  assert (Hy : forall y, awaiter y = awaiter x -> waiter y = waiter x -> sub y = sub x ->
             queue y = rest -> AInv L y /\
             (forall f tok, dpair t = Some (f, tok) -> awaiter x = Some (f, tok) ->
                AInv L (set_awaiter y None))).
  { intros y Ha Hw Hs Hq; split.
    - apply (step_ainv_same _ x); auto; intros u Hu; rewrite Hq in Hu; auto.
    - intros f tok Hd Ha'.
      destruct (proj2 (a_queue _ _ AI t f tok (ltac:(rewrite Q; left; auto)) Hd) Ha')
        as [Hw' Hs'].
      apply (step_ainv_cleared _ _ _ AI); fields; rewrite ?Hw, ?Hs; auto.
      intros u Hu; rewrite Hq in Hu; auto. }
  assert (Hx1 : exists y, (match task_action t with Some a => emit y0 a | None => y0 end) = y
             /\ awaiter y = awaiter x /\ waiter y = waiter x /\ sub y = sub x /\
             queue y = rest) by (destruct t; cbn; eexists; repeat split; reflexivity).
  destruct Hx1 as [y [Ey [Ha [Hw [Hs Hq]]]]]; rewrite Ey.
  destruct (Hy y Ha Hw Hs Hq) as [A1 A2].
  destruct t as [| tid | f tok o | f tok | f tok | f]; auto;
    rewrite Ha; destruct (awaiter x) as [a |] eqn:Ea; auto;
    destruct (pair_eqb a (f, tok)) eqn:Ep; auto;
    apply step_pair_eqb_true in Ep; subst a; apply (A2 f tok); auto.
Qed.
