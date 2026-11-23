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

(** The number of queued deliveries for the await of [p]. *)
Definition cnt (p : FiberId * Token) (q : list Task) : nat :=
  length (filter (fun t => match dpair t with Some p' => pair_eqb p' p | None => false end) q).

Definition init_or_none (s : option Sub) : Prop :=
  s = None \/ exists c, s = Some (SSample c FInitial).

(** A held cancellation, or one queued for the awaiter, exists only while no operation or
    awaited sample is subscribed; a queued cancellation is the only delivery for its await. *)
Record HInv (x : XState) : Prop := {
  h_held : held x = true -> init_or_none (sub x);
  h_dc : forall f tok, In (DeliverCancel f tok) (queue x) ->
         awaiter x = Some (f, tok) /\ init_or_none (sub x) /\ cnt (f, tok) (queue x) = 1%nat
}.

Definition ASInv (L : list LogEntry) (x : XState) : Prop := phase x = POpen -> AInv L x.

Definition SInv (L : list LogEntry) (x : XState) : Prop :=
  phase x = POpen -> AInv L x /\ HInv x.

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
  HInv x -> NoDup (start_tokens (L ++ [LEvent (EvStart f tok op)])) ->
  ASInv (L ++ [LEvent (EvStart f tok op)]) (on_start I x f tok op).
Proof.
  intros I x f tok op L [HI [HA _]] P AI HH Hnd Py.
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
        { destruct (h_held _ HH Hh) as [S0 | [c S0]]; rewrite S0; cbn; auto. }
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
  intros x f tok L [HI [HA _]] P AI; rewrite step_on_release_split.
  destruct (step_release_pre_fields x f tok) as (Hp & Hs & Ha & Hw & _ & _ & Hq & _).
  assert (AY : AInv L (release_pre x f tok))
    by (apply (step_ainv_same _ x); auto; intros t Ht; left; auto).
  assert (Hf : follows_pair (sub x) = None).
  { destruct (follows_pair (sub x)) eqn:E; auto.
    apply step_follows_active in E; congruence. }
  generalize dependent (release_pre x f tok); intros y Hp Hs Ha Hw Hq AY.
  unfold release_rest; rewrite Hp, P, Ha.
  destruct (awaiter x) as [a |] eqn:Ea; [| exact AY].
  destruct (negb (pair_eqb a (f, tok))) eqn:Ep; [exact AY |].
  apply negb_false_iff, step_pair_eqb_true in Ep; subst a.
  cbv zeta; rewrite Hw, Hs.
  destruct (waiter x) as [w |] eqn:W.
  - apply (step_ainv_cleared _ _ _ AY); fields; rewrite ?Hs; auto.
    destruct (a_slot _ _ AI) as [S0 | S0]; [congruence | | apply step_slot_not_sop; auto].
    rewrite S0; cbn; auto.
  - destruct (sub x) as [s |] eqn:S0.
    + destruct (release_sub s) as [[[f' tok'] s'] |] eqn:R.
      * destruct (step_release_sub_cases s f' tok' s' R) as (c & f0 & tok0 & op & k & rest &
          E1 & E2); [exact HA |]; subst s s'.
        rewrite step_release_sub_sop in R; inversion R; subst f' tok'.
        pose proof (a_sop _ _ AI c f0 tok0 op k rest S0) as Ha'; rewrite Ea in Ha'.
        inversion Ha'; subst f0 tok0; rewrite step_pair_eqb_refl.
        apply (step_ainv_cleared _ _ _ AY); fields; cbn; auto.
      * apply (step_ainv_cleared _ _ _ AY); fields; rewrite ?Hs, ?S0; auto.
        destruct s; cbn; auto; discriminate.
    + apply (step_ainv_cleared _ _ _ AY); fields; rewrite ?Hs, ?S0; cbn; auto.
Qed.

Lemma step_asinv_event : forall I x e L, IInv x -> SInv L x ->
  NoDup (start_tokens (L ++ [LEvent e])) -> ASInv (L ++ [LEvent e]) (on_event I x e).
Proof.
  intros I x e L HI SI Hnd Py.
  destruct (phase x) eqn:P.
  2,3: exfalso; revert Py; apply step_on_event_closed; congruence.
  destruct (SI P) as [AI HH].
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

(** ** Held cancellations *)

Lemma step_cnt_app : forall p a b, cnt p (a ++ b) = (cnt p a + cnt p b)%nat.
Proof. intros; unfold cnt; rewrite filter_app, length_app; reflexivity. Qed.

Lemma step_cnt_in : forall p q t, In t q -> dpair t = Some p -> (1 <= cnt p q)%nat.
Proof.
  intros p q t Ht Hd; unfold cnt.
  assert (H : In t (filter (fun t => match dpair t with Some p' => pair_eqb p' p
                                     | None => false end) q))
    by (apply filter_In; rewrite Hd, step_pair_eqb_refl; auto).
  destruct (filter _ q); [contradiction | cbn; lia].
Qed.

Lemma step_cnt_filter : forall p g q, (cnt p (filter g q) <= cnt p q)%nat.
Proof.
  intros p g q; induction q as [| t q IH]; cbn; auto.
  destruct (g t); cbn; unfold cnt in *; cbn;
    destruct (match dpair t with Some p' => pair_eqb p' p | None => false end); cbn; lia.
Qed.

Lemma step_cnt_cons : forall p t q, cnt p (t :: q) =
  ((if match dpair t with Some p' => pair_eqb p' p | None => false end then 1 else 0) +
   cnt p q)%nat.
Proof.
  intros; unfold cnt; cbn;
    destruct (match dpair t with Some p' => pair_eqb p' p | None => false end); reflexivity.
Qed.

Lemma step_cnt_none : forall p t, dpair t = None -> cnt p [t] = 0%nat.
Proof. intros p t H; unfold cnt; cbn; rewrite H; reflexivity. Qed.

Lemma step_cnt_other : forall p t q, (forall p', dpair t = Some p' -> p' <> p) ->
  cnt p (q ++ [t]) = cnt p q.
Proof.
  intros p t q H; rewrite step_cnt_app; unfold cnt at 2; cbn.
  destruct (dpair t) as [p' |] eqn:E; [| cbn; lia].
  destruct (pair_eqb p' p) eqn:Ep; [apply step_pair_eqb_true in Ep; exfalso; eapply H; eauto |].
  cbn; lia.
Qed.

Lemma step_dropped_true : forall x f tok, dropped_cancel x f tok = true ->
  In (DeliverCancel f tok) (queue x).
Proof.
  intros x f tok H; unfold dropped_cancel in H; apply existsb_exists in H.
  destruct H as [t [Ht Hm]]; destruct t; try discriminate.
  apply andb_true_iff in Hm; destruct Hm as [H1 H2].
  apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2; subst; auto.
Qed.

Lemma step_dropped_false : forall x f tok, dropped_cancel x f tok = false ->
  ~ In (DeliverCancel f tok) (queue x).
Proof.
  intros x f tok H Hin; unfold dropped_cancel in H.
  assert (E : existsb (fun t => match t with
                    | DeliverCancel f' tok' => Nat.eqb f f' && Nat.eqb tok tok'
                    | _ => false end) (queue x) = true)
    by (apply existsb_exists; exists (DeliverCancel f tok); rewrite !Nat.eqb_refl; auto).
  congruence.
Qed.

(** A state in which no cancellation is queued. *)
Lemma step_hinv_nodc : forall y, (held y = true -> init_or_none (sub y)) ->
  (forall f tok, ~ In (DeliverCancel f tok) (queue y)) -> HInv y.
Proof. intros y H1 H2; constructor; auto; intros f tok H; exfalso; eapply H2; eauto. Qed.

(** A state whose queued cancellations were all queued, with the same awaiter and
    subscription, before. *)
Lemma step_hinv_sub : forall x y, HInv x -> held y = held x -> sub y = sub x ->
  awaiter y = awaiter x ->
  (forall f tok, In (DeliverCancel f tok) (queue y) -> In (DeliverCancel f tok) (queue x)) ->
  (forall f tok, In (DeliverCancel f tok) (queue x) ->
     (cnt (f, tok) (queue y) <= cnt (f, tok) (queue x))%nat) -> HInv y.
Proof.
  intros x y [H1 H2] Hh Hs Ha Hq Hc; constructor; rewrite ?Hh, ?Hs, ?Ha; auto.
  intros f tok Hin; destruct (H2 f tok (Hq _ _ Hin)) as [A [B C]]; repeat split; auto.
  pose proof (Hc f tok (Hq _ _ Hin)); pose proof (step_cnt_in (f, tok) _ _ Hin eq_refl); lia.
Qed.

Lemma step_hinv_same : forall x y, HInv x -> held y = held x -> sub y = sub x ->
  awaiter y = awaiter x -> queue y = queue x -> HInv y.
Proof.
  intros x y H Hh Hs Ha Hq; apply (step_hinv_sub x); auto; rewrite Hq; auto.
Qed.

Lemma step_issue_op_held : forall I x f tok op, held (issue_op I x f tok op) = held x.
Proof.
  intros; unfold issue_op, issue; destruct op as [k a | d];
    [| destruct (match d with Millis m => split m | Forever => (max_chunk, Endless) end)];
    cbv zeta; destruct (nth_error (persisted I) (next_cmd x));
    try (match goal with |- context [cmd_eqb ?a ?b] => destruct (cmd_eqb a b) end);
    reflexivity.
Qed.

Lemma step_hinv_start : forall I x f tok op L, IInv x -> phase x = POpen -> AInv L x ->
  HInv x -> NoDup (start_tokens (L ++ [LEvent (EvStart f tok op)])) ->
  phase (on_start I x f tok op) = POpen -> HInv (on_start I x f tok op).
Proof.
  intros I x f tok op L HII P AI HH Hnd Py.
  pose proof (step_nodup_new _ _ _ _ Hnd) as Hn.
  assert (Hq : forall t f' tok', In t (queue x) -> dpair t = Some (f', tok') -> tok' <> tok).
  { intros t f' tok' Ht Hd E; subst; apply Hn; exact (proj1 (a_queue _ _ AI t f' tok Ht Hd)). }
  assert (Hc0 : forall f', cnt (f', tok) (queue x) = 0%nat).
  { intros f'; destruct (cnt (f', tok) (queue x)) eqn:E; auto; exfalso.
    unfold cnt in E.
    destruct (filter _ (queue x)) as [| t r] eqn:F; [discriminate |].
    assert (Ht : In t (filter (fun t => match dpair t with Some p' => pair_eqb p' (f', tok)
                                        | None => false end) (queue x))) by (rewrite F; left; auto).
    apply filter_In in Ht; destruct Ht as [Ht Hm].
    destruct (dpair t) as [[g tk] |] eqn:Hd; [| discriminate].
    apply step_pair_eqb_true in Hm; inversion Hm; subst; exact (Hq t _ _ Ht Hd eq_refl). }
  assert (Hnodc : awaiter x = None -> forall g tk, ~ In (DeliverCancel g tk) (queue x)).
  { intros Ea g tk Hin; destruct (h_dc _ HH g tk Hin) as [A _]; congruence. }
  unfold on_start in *; rewrite P in *; cbv zeta in *.
  destruct (zero_sleep op).
  - apply (step_hinv_sub x); fields; auto.
    + intros g tk Ht; apply in_app_or in Ht; destruct Ht as [Ht | [Ht | []]]; auto;
        discriminate.
    + intros g tk Hin; rewrite step_cnt_app; unfold cnt at 2; cbn.
      destruct (pair_eqb (f, tok) (g, tk)) eqn:E; cbn; [| lia].
      apply step_pair_eqb_true in E; inversion E; subst.
      exfalso; destruct (h_dc _ HH g tk Hin) as [A _].
      apply Hn; exact (a_tok _ _ AI g tk A).
  - fields; destruct (awaiter x) as [a |] eqn:Ea.
    + rewrite (step_violate_stays _ _ Py); apply (step_hinv_same x); auto.
    + destruct (held x) eqn:Hh.
      * constructor; fields; [discriminate |].
        intros g tk Hin; apply in_app_or in Hin; destruct Hin as [Hin | [Hin | []]].
        -- exfalso; exact (Hnodc eq_refl g tk Hin).
        -- inversion Hin; subst; split; [auto | split; [exact (h_held _ HH Hh) |]].
           rewrite step_cnt_app, Hc0; unfold cnt; cbn; rewrite step_pair_eqb_refl; auto.
      * destruct (slot_held _).
        -- apply step_hinv_nodc; fields; [rewrite Hh; discriminate |].
           exact (Hnodc eq_refl).
        -- destruct (step_issue_op_stays _ _ _ _ _ Py) as (H1 & H2 & H3 & _).
           apply step_hinv_nodc; rewrite ?H3, ?step_issue_op_held; fields;
             [rewrite Hh; discriminate | exact (Hnodc eq_refl)].
Qed.

Lemma step_hinv_release : forall x f tok L, IInv x -> phase x = POpen -> AInv L x ->
  HInv x -> HInv (on_release x f tok).
Proof.
  intros x f tok L [HI [HA _]] P AI HH; rewrite step_on_release_split.
  destruct (step_release_pre_fields x f tok) as (Hp & Hs & Ha & Hw & _ & _ & Hq & _).
  assert (Hdc : forall g tk, In (DeliverCancel g tk) (queue (release_pre x f tok)) ->
            In (DeliverCancel g tk) (queue x) /\ (g, tk) <> (f, tok)).
  { intros g tk Hin; split; [auto |].
    unfold release_pre in Hin; rewrite P in Hin; cbv zeta in Hin.
    intros E; inversion E; subst.
    destruct (dropped_cancel x f tok); fields; apply filter_In in Hin; destruct Hin as [_ Hm];
      cbn in Hm; rewrite !Nat.eqb_refl in Hm; discriminate. }
  assert (Hcnt : forall g tk, In (DeliverCancel g tk) (queue x) ->
            (cnt (g, tk) (queue (release_pre x f tok)) <= cnt (g, tk) (queue x))%nat).
  { intros g tk _; unfold release_pre; rewrite P; cbv zeta;
      destruct (dropped_cancel x f tok); fields; apply step_cnt_filter. }
  destruct (dropped_cancel x f tok) eqn:D.
  - (* A dropped cancellation is held again. *)
    pose proof (step_dropped_true _ _ _ D) as D0.
    destruct (h_dc _ HH f tok D0) as [Ea [Hio _]].
    assert (Hwn : waiter x = None)
      by exact (proj1 (proj2 (a_queue _ _ AI _ f tok D0 eq_refl) Ea)).
    assert (Hheld : held (release_pre x f tok) = true)
      by (unfold release_pre; rewrite P; cbv zeta; rewrite D; reflexivity).
    generalize dependent (release_pre x f tok); intros y Hp Hs Ha Hw Hq Hdc Hcnt Hheld.
    assert (Hnone : forall g tk, ~ In (DeliverCancel g tk) (queue y)).
    { intros g tk Hin; destruct (Hdc g tk Hin) as [Hin' Hne].
      destruct (h_dc _ HH g tk Hin') as [A _]; congruence. }
    unfold release_rest; rewrite Hp, P, Ha, Ea, step_pair_eqb_refl; cbn [negb].
    cbv zeta; rewrite Hw, Hwn, Hs.
    destruct Hio as [S0 | [c S0]]; rewrite S0; cbn [release_sub];
      apply step_hinv_nodc; fields; rewrite ?Hs, ?S0; auto; intros _; [left | right; eauto];
      auto.
  - apply step_dropped_false in D.
    assert (Hheld : held (release_pre x f tok) = held x)
      by (unfold release_pre; rewrite P; cbv zeta;
          destruct (dropped_cancel x f tok) eqn:D'; [apply step_dropped_true in D'; tauto |];
          reflexivity).
    assert (HY : HInv (release_pre x f tok)).
    { apply (step_hinv_sub x); auto; intros g tk Hin; apply (Hdc g tk Hin). }
    generalize dependent (release_pre x f tok); intros y Hp Hs Ha Hw Hq Hdc Hcnt Hheld HY.
    unfold release_rest; rewrite Hp, P, Ha.
    destruct (awaiter x) as [a |] eqn:Ea; [| exact HY].
    destruct (negb (pair_eqb a (f, tok))) eqn:Ep; [exact HY |].
    apply negb_false_iff, step_pair_eqb_true in Ep; subst a.
    (* The awaiter's own cancellation was not queued, so none is. *)
    assert (Hnone : forall g tk, ~ In (DeliverCancel g tk) (queue y)).
    { intros g tk Hin; destruct (Hdc g tk Hin) as [Hin' _].
      destruct (h_dc _ HH g tk Hin') as [A _]; rewrite Ea in A; inversion A; subst.
      exact (D Hin'). }
    cbv zeta; rewrite Hw, Hs.
    destruct (waiter x) as [w |].
    + apply step_hinv_nodc; fields; rewrite ?Hheld, ?Hs; auto; exact (h_held _ HH).
    + destruct (sub x) as [s |] eqn:S0.
      * destruct (release_sub s) as [[[f' tok'] s'] |] eqn:R.
        -- destruct (pair_eqb _ _).
           ++ apply step_hinv_nodc; fields; auto.
              intros H; rewrite Hheld in H; destruct (h_held _ HH H) as [E | [c E]];
                rewrite S0 in E; [discriminate |].
              inversion E; subst; discriminate.
           ++ apply step_hinv_nodc; fields; rewrite ?Hheld, ?Hs, ?S0; auto.
              intros H; rewrite <- S0; exact (h_held _ HH H).
        -- apply step_hinv_nodc; fields; rewrite ?Hheld, ?Hs, ?S0; auto.
           intros H; rewrite <- S0; exact (h_held _ HH H).
      * apply step_hinv_nodc; fields; rewrite ?Hheld, ?Hs, ?S0; auto.
        intros H; rewrite <- S0; exact (h_held _ HH H).
Qed.

Lemma step_hinv_event : forall I x e L, IInv x -> phase x = POpen -> AInv L x -> HInv x ->
  NoDup (start_tokens (L ++ [LEvent e])) -> phase (on_event I x e) = POpen ->
  HInv (on_event I x e).
Proof.
  intros I x e L HI P AI HH Hnd Py; unfold on_event in *; rewrite P in *.
  destruct e as [f tok op | f tok | pr t | f | r].
  - apply (step_hinv_start I x f tok op L); auto.
  - apply (step_hinv_release x f tok L); auto.
  - destruct (Nat.eqb pr 0).
    + apply (step_hinv_sub x); fields; auto.
      * intros g tk Ht; apply in_app_or in Ht; destruct Ht as [Ht | [Ht | []]]; auto;
          discriminate.
      * intros g tk _; rewrite step_cnt_app, step_cnt_none; auto; lia.
    + rewrite (step_violate_stays _ _ Py); auto.
  - apply (step_hinv_same x); auto.
  - destruct (root_exit x).
    + rewrite (step_violate_stays _ _ Py); auto.
    + rewrite (step_close_stays _ _ Py); apply (step_hinv_same x); auto.
Qed.

Lemma step_sinv_event : forall I x e L, IInv x -> SInv L x ->
  NoDup (start_tokens (L ++ [LEvent e])) -> SInv (L ++ [LEvent e]) (on_event I x e).
Proof.
  intros I x e L HI SI Hnd Py; split; [apply (step_asinv_event I x e L); auto |].
  destruct (phase x) eqn:P.
  2,3: exfalso; revert Py; apply step_on_event_closed; congruence.
  destruct (SI P) as [AI HH]; apply (step_hinv_event I x e L); auto.
Qed.

(** ** Inside a task *)

Lemma step_sinv_mono : forall L L' x, SInv L x ->
  (forall t, In t (start_tokens L) -> In t (start_tokens L')) -> SInv L' x.
Proof.
  intros L L' x H M P; destruct (H P); split; auto; apply (step_ainv_mono L); auto.
Qed.

Lemma step_sinv_same : forall L x y, SInv L x -> phase y = phase x ->
  awaiter y = awaiter x -> waiter y = waiter x -> sub y = sub x ->
  queue y = queue x -> held y = held x -> SInv L y.
Proof.
  intros L x y H P Ha Hw Hs Hq Hh Py; destruct H as [A B]; [congruence |]; split.
  - apply (step_ainv_same L x); auto; intros t Ht; rewrite Hq in Ht; auto.
  - apply (step_hinv_same x); auto.
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

Lemma step_hinv_head : forall x t rest, phase x = POpen -> queue x = t :: rest -> HInv x ->
  HInv (head_state x t rest).
Proof.
  intros x t rest P Q HH.
  assert (Hin : forall u, In u rest -> In u (queue x)) by (intros; rewrite Q; right; auto).
  assert (Hc : forall p, (cnt p rest <= cnt p (queue x))%nat)
    by (intros p; rewrite Q, step_cnt_cons; lia).
  unfold head_state; cbv zeta.
  set (y0 := set_progress (set_queue x rest) (S (progress x))).
  assert (Hx1 : exists y, (match task_action t with Some a => emit y0 a | None => y0 end) = y
             /\ awaiter y = awaiter x /\ held y = held x /\ sub y = sub x /\
             queue y = rest) by (destruct (task_action t); eexists; repeat split; reflexivity).
  destruct Hx1 as [y [Ey [Ha [Hh [Hs Hq]]]]]; rewrite Ey.
  assert (HY : HInv y) by (apply (step_hinv_sub x); rewrite ?Hq; auto).
  (* When the head clears the awaiter, no cancellation remains queued. *)
  assert (Hclr : forall f tok, dpair t = Some (f, tok) -> awaiter x = Some (f, tok) ->
            HInv (set_awaiter y None)).
  { intros f tok Hd Ea; apply step_hinv_nodc; fields; rewrite ?Hh, ?Hs;
      [exact (h_held _ HH) |].
    intros g tk Hr; rewrite Hq in Hr.
    destruct (h_dc _ HH g tk (Hin _ Hr)) as [A [_ C]]; rewrite Ea in A.
    injection A as <- <-.
    rewrite Q, step_cnt_cons, Hd, step_pair_eqb_refl in C.
    pose proof (step_cnt_in (f, tok) rest _ Hr eq_refl); lia. }
  destruct t as [| tid | f tok o | f tok | f tok | f]; auto;
    rewrite Ha; destruct (awaiter x) as [a |] eqn:Ea; auto;
    destruct (pair_eqb a (f, tok)) eqn:Ep; auto;
    apply step_pair_eqb_true in Ep; subst a; apply (Hclr f tok); auto.
Qed.

Lemma step_sinv_head : forall x t rest L, Inv x -> queue x = t :: rest -> SInv L x ->
  SInv (L ++ [LTask t]) (head_state x t rest).
Proof.
  intros x t rest L HI Q SI Py.
  destruct (step_head_state_closed x t rest) as [Hp _].
  assert (P : phase x = POpen) by congruence.
  destruct (SI P) as [AI HH]; split;
    [apply step_ainv_head | apply step_hinv_head]; auto.
Qed.
