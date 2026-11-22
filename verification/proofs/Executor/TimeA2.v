(** * The await invariant across the transitions that change an await's standing.

    A start, a queued delivery or cancellation, a waiter, a command issued for an await, a
    sample command, and an applied sample. Each lemma states what the transition needs of
    the state before it. *)

From Coq Require Import List ZArith Bool Arith Lia Sorting.
From Durable Require Import Runtime Exec Rev3 Statements TimeBase TimeStep TimeL TimeA.
Import ListNotations.
Open Scope Z_scope.

Lemma time_pair_dec : forall (f g : FiberId) (tok t : Token),
  {f = g /\ tok = t} + {~ (f = g /\ tok = t)}.
Proof.
  intros. destruct (Nat.eq_dec f g), (Nat.eq_dec tok t); [left|right..]; tauto.
Qed.

Lemma time_is_start_other : forall g t f tok op,
  ~ (g = f /\ t = tok) -> time_is_start g t (AStart f tok op) = false.
Proof.
  intros g t f tok op H. cbn. destruct (Nat.eqb g f) eqn:E1, (Nat.eqb t tok) eqn:E2; auto.
  apply Nat.eqb_eq in E1, E2. tauto.
Qed.

Lemma time_after_last_start_some : forall f tok t b mid,
  time_after_last (time_is_start f tok) t = Some (b, mid) -> exists op, b = AStart f tok op.
Proof.
  intros f tok t b mid H. apply time_after_last_some in H as [H _].
  destruct b; try discriminate. apply time_eqb_pair in H as [-> ->]. eauto.
Qed.

Lemma time_existsb_start_some : forall f tok t,
  existsb (time_is_start f tok) t = true ->
  exists op mid, time_after_last (time_is_start f tok) t = Some (AStart f tok op, mid).
Proof.
  intros f tok t H. destruct (time_existsb_after_last _ _ H) as [b [mid E]].
  destruct (time_after_last_start_some _ _ _ _ _ E) as [op ->]. eauto.
Qed.

Lemma time_after_last_existsb : forall p t b s,
  time_after_last p t = Some (b, s) -> existsb p t = true.
Proof.
  intros p t b s H. apply time_after_last_some in H as [H1 [_ [pre ->]]].
  rewrite existsb_app. cbn. rewrite H1. apply orb_true_r.
Qed.

(** ** A start *)

Lemma time_inva_start : forall x f tok op,
  time_inva x -> NoDup (time_stoks (trace x ++ [AStart f tok op])) ->
  time_inva (emit x (AStart f tok op)).
Proof.
  intros x f tok op Hx N.
  assert (Fr : existsb (time_is_start f tok) (trace x) = false) by (eapply time_fresh; exact N).
  assert (Fd : time_nodel f tok (queue x)).
  { intros o I0. rewrite (ta_r1 x Hx f tok o I0) in Fr. discriminate. }
  assert (Fc : ~ In (DeliverCancel f tok) (queue x)).
  { intros I0. rewrite (ta_r2 x Hx f tok I0) in Fr. discriminate. }
  assert (Fw : time_waiter_is f tok (waiter x) = false).
  { destruct (waiter x) as [[[g t] op']|] eqn:W; [|reflexivity]. cbn.
    destruct (Nat.eqb f g) eqn:E1, (Nat.eqb tok t) eqn:E2; auto.
    apply Nat.eqb_eq in E1, E2. subst.
    destruct (ta_r3 x Hx g t op' W) as [[mid [M _]] _].
    apply time_after_last_existsb in M. congruence. }
  assert (Fs : time_sub_refs f tok (sub x) = false).
  { destruct (time_sub_refs f tok (sub x)) eqn:E; [|reflexivity].
    destruct (ta_r4 x Hx f tok E) as [[op' [mid [M _]]] _].
    apply time_after_last_existsb in M. congruence. }
  assert (Fl : time_sub_live f tok (sub x) = false).
  { destruct (sub x) as [[]|]; cbn in Fs |- *; auto. destruct after; auto. }
  assert (Ext : forall p, p (AStart f tok op) = false ->
     time_after_last p (trace x ++ [AStart f tok op]) =
     match time_after_last p (trace x) with Some (b, s) => Some (b, s ++ [AStart f tok op])
     | None => None end).
  { intros p Hp. rewrite time_after_last_snoc, Hp. reflexivity. }
  assert (Own : forall g t, time_is_owned g t (AStart f tok op) = false) by reflexivity.
  constructor; unfold time_waiting, time_refd, time_since_credits, time_ldinv, time_p7_ok,
    time_p8a_ok, time_p8b_ok; tsimp.
  - intros g t o I0. apply time_existsb_app_true. exact (ta_r1 x Hx g t o I0).
  - intros g t I0. apply time_existsb_app_true. exact (ta_r2 x Hx g t I0).
  - intros g t op' W. destruct (ta_r3 x Hx g t op' W) as [[mid [M1 M2]] [O [A [Id [Dl Dc]]]]].
    assert (Ne : ~ (g = f /\ t = tok)).
    { intros [-> ->]. apply time_after_last_existsb in M1. congruence. }
    split; [|split; [|split; [|split; [|split]]]]; auto.
    + exists (mid ++ [AStart f tok op]). rewrite Ext, M1 by (apply time_is_start_other; exact Ne).
      split; [reflexivity|]. rewrite existsb_app, M2. reflexivity.
    + rewrite existsb_app, O. reflexivity.
  - intros g t R. destruct (ta_r4 x Hx g t R) as [[op' [mid [M1 M2]]] Sc].
    assert (Ne : ~ (g = f /\ t = tok)).
    { intros [-> ->]. congruence. }
    split.
    + exists op', (mid ++ [AStart f tok op]).
      rewrite Ext, M1 by (apply time_is_start_other; exact Ne).
      split; [reflexivity|]. apply time_existsb_app_true. exact M2.
    + rewrite Ext by apply Own. unfold time_since_credits in Sc.
      destruct (time_after_last (time_is_owned g t) (trace x)) as [[b s]|]; [|exact I].
      rewrite time_credits_app, Sc. reflexivity.
  - intros g t O. rewrite existsb_app, orb_false_r in O.
    apply time_existsb_app_true. exact (ta_owned x Hx g t O).
  - intros g t. destruct (time_pair_dec g f t tok) as [[-> ->]|Ne].
    + rewrite time_after_last_snoc. cbn. rewrite !Nat.eqb_refl. cbn. intros _.
      split; [constructor|]. right; right; right; right; right. auto.
    + pose proof (ta_ld x Hx g t) as L. unfold time_ldinv in L.
      rewrite Ext by (apply time_is_start_other; exact Ne).
      destruct (time_after_last (time_is_start g t) (trace x)) as [[b mid]|]; [|exact I].
      destruct b; try exact I. intros Sl.
      apply (time_ld_frame g t op0 mid _ x _ (L Sl)); tsimp; auto.
      * rewrite time_credits_app. cbn. apply app_nil_r.
      * intros op' E. exact (proj1 (proj2 (proj2 (proj2 (proj2 (ta_r3 x Hx g t op' E)))))).
      * intros [[f' t'] op'] E.
        exact (proj1 (proj2 (proj2 (proj2 (ta_r3 x Hx f' t' op' E))))).
  - intros g t o I0. pose proof (ta_p7 x Hx g t o I0) as H. unfold time_p7_ok in H.
    rewrite Ext by apply Own.
    destruct (time_after_last (time_is_owned g t) (trace x)) as [[b s]|]; [|exact I].
    apply time_existsb_app_true. exact H.
  - intros g t I0. destruct (ta_p8 x Hx g t I0) as [Ha Hb].
    unfold time_p8a_ok, time_p8b_ok in *.
    assert (Ne : ~ (g = f /\ t = tok)) by (intros [-> ->]; contradiction).
    split.
    + rewrite Ext by apply Own.
      destruct (time_after_last (time_is_owned g t) (trace x)) as [[b s]|]; [|exact I].
      destruct Ha as [Ha1 Ha2]. split; [apply time_existsb_app_true; exact Ha1|].
      rewrite time_credits_app, Ha2. reflexivity.
    + rewrite Ext by (apply time_is_start_other; exact Ne).
      destruct (time_after_last (time_is_start g t) (trace x)) as [[b mid]|]; [|exact I].
      rewrite !existsb_app. cbn. rewrite !orb_false_r. exact Hb.
  - apply time_claims_snoc; [exact (ta_claims x Hx)|exact I].
Qed.

(** ** Queued deliveries and cancellations *)

Lemma time_waiter_ne : forall x f tok g t op,
  time_waiter_is f tok (waiter x) = false -> waiter x = Some (g, t, op) -> ~ (g = f /\ t = tok).
Proof.
  intros x f tok g t op H W [-> ->]. rewrite W in H. cbn in H. rewrite !Nat.eqb_refl in H.
  discriminate.
Qed.

Lemma time_r3_nodel : forall x, time_inva x ->
  forall g t op', waiter x = Some (g, t, op') -> time_nodel g t (queue x).
Proof.
  intros x Hx g t op' E. exact (proj1 (proj2 (proj2 (proj2 (proj2 (ta_r3 x Hx g t op' E)))))).
Qed.

Lemma time_r3_idle : forall x, time_inva x ->
  forall w, waiter x = Some w -> time_idle (sub x) = true.
Proof.
  intros x Hx [[g t] op'] E. exact (proj1 (proj2 (proj2 (proj2 (ta_r3 x Hx g t op' E))))).
Qed.

Lemma time_inva_enq_deliver : forall x f tok o,
  time_inva x ->
  existsb (time_is_start f tok) (trace x) = true ->
  time_p7_ok f tok (trace x) ->
  time_waiter_is f tok (waiter x) = false ->
  (forall op mid, time_after_last (time_is_start f tok) (trace x) =
                  Some (AStart f tok op, mid) -> time_sleepy op ->
     time_total_ok op (credits f tok mid) /\ time_sub_live f tok (sub x) = false) ->
  time_inva (enqueue x (Deliver f tok o)).
Proof.
  intros x f tok o Hx Hs H7 Hw HL. unfold enqueue.
  assert (Q : forall t, In t (queue x ++ [Deliver f tok o]) ->
              In t (queue x) \/ t = Deliver f tok o).
  { intros t I0. apply in_app_or in I0 as [I0|[<-|[]]]; auto. }
  assert (Nd : forall g t, ~ (g = f /\ t = tok) -> time_nodel g t (queue x) ->
               time_nodel g t (queue x ++ [Deliver f tok o])).
  { intros g t Ne N o' I0. destruct (Q _ I0) as [I1|I1]; [exact (N o' I1)|].
    inversion I1; subst. tauto. }
  constructor; unfold time_waiting, time_refd, time_since_credits, time_ldinv, time_p7_ok,
    time_p8a_ok, time_p8b_ok; tsimp.
  - intros g t o' I0. destruct (Q _ I0) as [I1|I1]; [exact (ta_r1 x Hx g t o' I1)|].
    inversion I1; subst. exact Hs.
  - intros g t I0. destruct (Q _ I0) as [I1|I1]; [exact (ta_r2 x Hx g t I1)|discriminate].
  - intros g t op' W. destruct (ta_r3 x Hx g t op' W) as [M [O [A [Id [Dl Dc]]]]].
    split; [exact M|]. split; [exact O|]. split; [exact A|]. split; [exact Id|].
    split; [apply Nd; [eapply time_waiter_ne; eauto|exact Dl]|].
    intros I0. destruct (Q _ I0) as [I1|I1]; [exact (Dc I1)|discriminate].
  - exact (ta_r4 x Hx).
  - exact (ta_owned x Hx).
  - intros g t. pose proof (ta_ld x Hx g t) as L. unfold time_ldinv in L.
    destruct (time_after_last (time_is_start g t) (trace x)) as [[b mid]|] eqn:E;
      [|exact I].
    destruct b; try exact I. intros Sl. specialize (L Sl).
    destruct (time_pair_dec g f t tok) as [[-> ->]|Ne].
    + destruct (time_after_last_start_some _ _ _ _ _ E) as [op' Eo]. inversion Eo; subst.
      destruct (HL op' mid E Sl) as [T Lv]. split; [exact (proj1 L)|].
      right; right; right; right; left. tsimp. auto.
    + apply (time_ld_frame g t op mid mid x _ L); tsimp; auto.
      * intros op' E'. eapply time_r3_nodel; eauto.
      * apply time_r3_idle. exact Hx.
  - intros g t o' I0. destruct (Q _ I0) as [I1|I1]; [exact (ta_p7 x Hx g t o' I1)|].
    inversion I1; subst. exact H7.
  - intros g t I0. destruct (Q _ I0) as [I1|I1]; [exact (ta_p8 x Hx g t I1)|discriminate].
  - exact (ta_claims x Hx).
Qed.

Lemma time_inva_enq_cancel : forall x f tok,
  time_inva x ->
  existsb (time_is_start f tok) (trace x) = true ->
  time_p8a_ok f tok (trace x) -> time_p8b_ok f tok (trace x) ->
  time_waiter_is f tok (waiter x) = false ->
  time_inva (enqueue x (DeliverCancel f tok)).
Proof.
  intros x f tok Hx Hs Ha Hb Hw. unfold enqueue.
  assert (Q : forall t, In t (queue x ++ [DeliverCancel f tok]) ->
              In t (queue x) \/ t = DeliverCancel f tok).
  { intros t I0. apply in_app_or in I0 as [I0|[<-|[]]]; auto. }
  assert (Nd : forall g t, time_nodel g t (queue x) ->
               time_nodel g t (queue x ++ [DeliverCancel f tok])).
  { intros g t N o' I0. destruct (Q _ I0) as [I1|I1]; [exact (N o' I1)|discriminate]. }
  constructor; unfold time_waiting, time_refd, time_since_credits, time_ldinv, time_p7_ok,
    time_p8a_ok, time_p8b_ok; tsimp.
  - intros g t o' I0. destruct (Q _ I0) as [I1|I1]; [exact (ta_r1 x Hx g t o' I1)|discriminate].
  - intros g t I0. destruct (Q _ I0) as [I1|I1]; [exact (ta_r2 x Hx g t I1)|].
    inversion I1; subst. exact Hs.
  - intros g t op' W. destruct (ta_r3 x Hx g t op' W) as [M [O [A [Id [Dl Dc]]]]].
    split; [exact M|]. split; [exact O|]. split; [exact A|]. split; [exact Id|].
    split; [apply Nd; exact Dl|].
    intros I0. destruct (Q _ I0) as [I1|I1]; [exact (Dc I1)|].
    inversion I1; subst. eapply time_waiter_ne; eauto.
  - exact (ta_r4 x Hx).
  - exact (ta_owned x Hx).
  - intros g t. pose proof (ta_ld x Hx g t) as L. unfold time_ldinv in L.
    destruct (time_after_last (time_is_start g t) (trace x)) as [[b mid]|]; [|exact I].
    destruct b; try exact I. intros Sl.
    apply (time_ld_frame g t op mid mid x _ (L Sl)); tsimp; auto.
    + intros op' E'. eapply time_r3_nodel; eauto.
    + apply time_r3_idle. exact Hx.
  - intros g t o' I0. destruct (Q _ I0) as [I1|I1]; [exact (ta_p7 x Hx g t o' I1)|discriminate].
  - intros g t I0. destruct (Q _ I0) as [I1|I1]; [exact (ta_p8 x Hx g t I1)|].
    inversion I1; subst. split; assumption.
  - exact (ta_claims x Hx).
Qed.

(** ** A fiber waits for the slot *)

Lemma time_inva_set_waiter : forall x f tok op,
  time_inva x -> waiter x = None ->
  time_waiting f tok op (set_waiter x (Some (f, tok, op))) ->
  time_inva (set_waiter x (Some (f, tok, op))).
Proof.
  intros x f tok op Hx W0 Hw.
  constructor; unfold time_ldinv; tsimp.
  - exact (ta_r1 x Hx).
  - exact (ta_r2 x Hx).
  - intros g t op' E. inversion E; subst. exact Hw.
  - intros g t R. destruct (ta_r4 x Hx g t R) as [A B]. split; assumption.
  - exact (ta_owned x Hx).
  - intros g t. pose proof (ta_ld x Hx g t) as L. unfold time_ldinv in L.
    destruct (time_after_last (time_is_start g t) (trace x)) as [[b mid]|] eqn:E;
      [|exact I].
    destruct b; try exact I. intros Sl. destruct (L Sl) as [B St]. split; [exact B|].
    destruct (time_pair_dec g f t tok) as [[-> ->]|Ne].
    + destruct Hw as [[mid' [M1 M2]] _]. tsimp. rewrite E in M1. inversion M1; subst.
      right; left. split; [reflexivity|]. apply time_credits_nil_samples. exact M2.
    + rewrite W0 in St.
      destruct St as [PD|[[S1 _]|[S2|[S3|[[T [Lv Wv]]|[Dl [Lv Wv]]]]]]]; tsimp.
      * left. exact PD.
      * discriminate.
      * right; right; left. exact S2.
      * right; right; right; left. exact S3.
      * right; right; right; right; left. split; [exact T|]. split; [exact Lv|].
        cbn. destruct (Nat.eqb g f) eqn:E1, (Nat.eqb t tok) eqn:E2; auto.
        apply Nat.eqb_eq in E1, E2. tauto.
      * right; right; right; right; right. split; [exact Dl|]. split; [exact Lv|].
        cbn. destruct (Nat.eqb g f) eqn:E1, (Nat.eqb t tok) eqn:E2; auto.
        apply Nat.eqb_eq in E1, E2. tauto.
  - exact (ta_p7 x Hx).
  - exact (ta_p8 x Hx).
  - exact (ta_claims x Hx).
Qed.

(** ** Commands *)

Lemma time_is_owned_other : forall g t f tok c k,
  ~ (g = f /\ t = tok) -> time_is_owned g t (ACommand c k (Some (f, tok))) = false.
Proof.
  intros g t f tok c k H. cbn. destruct (Nat.eqb g f) eqn:E1, (Nat.eqb tok t) eqn:E2; auto;
  destruct (Nat.eqb t tok) eqn:E3; auto; apply Nat.eqb_eq in E1, E3; tauto.
Qed.

(** A state's await standing for a pair other than the subscription's, once the
    subscription belongs to someone else and no fiber waits. *)
Lemma time_ld_away : forall g t op mid mid' x x',
  time_ld g t op mid x -> credits g t mid' = credits g t mid ->
  phase x' = phase x -> waiter x = None -> waiter x' = None ->
  queue x' = queue x -> time_sub_live g t (sub x') = false ->
  time_ld g t op mid' x'.
Proof.
  intros g t op mid mid' x x' [B St] C P W0 W1 Q Lv. unfold time_ld. rewrite C, P, W1, Q.
  split; [exact B|]. rewrite W0 in St.
  destruct St as [PD|[[S1 _]|[S2|[S3|[[T [_ _]]|[Dl [_ _]]]]]]].
  - left. exact PD.
  - discriminate.
  - destruct S2 as [c [d [k [rest [_ [_ [_ Nd]]]]]]].
    right; right; right; right; right. auto.
  - destruct S3 as [c [k [rest [_ [_ [_ Nd]]]]]].
    right; right; right; right; right. auto.
  - right; right; right; right; left. auto.
  - right; right; right; right; right. auto.
Qed.

Lemma time_live_sop_other : forall g t c f tok op k rest,
  ~ (g = f /\ t = tok) -> time_sub_live g t (Some (SOp c f tok op k rest)) = false.
Proof.
  intros. cbn. destruct (Nat.eqb g f) eqn:E1, (Nat.eqb t tok) eqn:E2; auto.
  apply Nat.eqb_eq in E1, E2. tauto.
Qed.

Lemma time_inva_issue_owned : forall x c k f tok n c' op' ch rest,
  time_inva x -> waiter x = None ->
  existsb (time_is_start f tok) (trace x) = true ->
  time_nodel f tok (queue x) -> ~ In (DeliverCancel f tok) (queue x) ->
  (forall op mid, time_after_last (time_is_start f tok) (trace x) =
                  Some (AStart f tok op, mid) -> time_sleepy op ->
     (exists d, op' = OSleep d) /\ 1 <= ch <= max_chunk /\
     time_chain_ok op (credits f tok mid) ch rest /\ time_bounds (credits f tok mid)) ->
  time_inva (set_sub (set_next_cmd (emit x (ACommand c k (Some (f, tok)))) n)
               (Some (SOp c' f tok op' ch rest))).
Proof.
  intros x c k f tok n c' op' ch rest Hx W0 Hs Dl Dc HL.
  set (a := ACommand c k (Some (f, tok))).
  assert (Ext : forall p, p a = false ->
     time_after_last p (trace x ++ [a]) =
     match time_after_last p (trace x) with Some (b, s) => Some (b, s ++ [a])
     | None => None end).
  { intros p Hp. rewrite time_after_last_snoc, Hp. reflexivity. }
  assert (St : forall g t, time_is_start g t a = false) by reflexivity.
  constructor; unfold time_waiting, time_refd, time_since_credits, time_ldinv, time_p7_ok,
    time_p8a_ok, time_p8b_ok; tsimp.
  - intros g t o I0. apply time_existsb_app_true. exact (ta_r1 x Hx g t o I0).
  - intros g t I0. apply time_existsb_app_true. exact (ta_r2 x Hx g t I0).
  - intros g t op E. congruence.
  - intros g t R. cbn in R. apply time_eqb_pair in R as [-> ->].
    destruct (time_existsb_start_some _ _ _ Hs) as [op0 [mid M]]. split.
    + exists op0, (mid ++ [a]). rewrite Ext, M by apply St. split; [reflexivity|].
      rewrite existsb_app. cbn. rewrite !Nat.eqb_refl. apply orb_true_r.
    + rewrite time_after_last_snoc. cbn. rewrite !Nat.eqb_refl. reflexivity.
  - intros g t O. apply time_existsb_app_true. rewrite existsb_app in O.
    destruct (existsb (time_is_owned g t) (trace x)) eqn:E;
      [exact (ta_owned x Hx g t E)|].
    change (existsb (time_is_owned g t) [a]) with (time_is_owned g t a || false) in O.
    destruct (time_pair_dec g f t tok) as [[-> ->]|Ne]; [exact Hs|].
    subst a. rewrite (time_is_owned_other g t f tok c k Ne) in O. discriminate.
  - intros g t. pose proof (ta_ld x Hx g t) as L. unfold time_ldinv in L.
    rewrite Ext by apply St.
    destruct (time_after_last (time_is_start g t) (trace x)) as [[b mid]|] eqn:E;
      [|exact I].
    destruct b; try exact I. intros Sl. specialize (L Sl).
    assert (Cr : credits g t (mid ++ [a]) = credits g t mid)
      by (rewrite time_credits_app; cbn; apply app_nil_r).
    destruct (time_pair_dec g f t tok) as [[-> ->]|Ne].
    + destruct (time_after_last_start_some _ _ _ _ _ E) as [op1 Eo]. inversion Eo; subst.
      destruct (HL op1 mid E Sl) as [[d ->] [K [Ch B]]].
      unfold time_ld. rewrite Cr. split; [exact B|]. right; right; left. tsimp.
      exists c', d, ch, rest. auto.
    + apply (time_ld_away g t op mid _ x _ L Cr); tsimp; auto.
      apply time_live_sop_other. exact Ne.
  - intros g t o I0. pose proof (ta_p7 x Hx g t o I0) as H. unfold time_p7_ok in H.
    assert (Ne : ~ (g = f /\ t = tok)) by (intros [-> ->]; exact (Dl o I0)).
    rewrite Ext by (apply time_is_owned_other; exact Ne).
    destruct (time_after_last (time_is_owned g t) (trace x)) as [[b s]|]; [|exact I].
    apply time_existsb_app_true. exact H.
  - intros g t I0. destruct (ta_p8 x Hx g t I0) as [Ha Hb].
    unfold time_p8a_ok, time_p8b_ok in *.
    assert (Ne : ~ (g = f /\ t = tok)) by (intros [-> ->]; exact (Dc I0)).
    split.
    + rewrite Ext by (apply time_is_owned_other; exact Ne).
      destruct (time_after_last (time_is_owned g t) (trace x)) as [[b s]|]; [|exact I].
      destruct Ha as [Ha1 Ha2]. split; [apply time_existsb_app_true; exact Ha1|].
      rewrite time_credits_app, Ha2. reflexivity.
    + rewrite Ext by apply St.
      destruct (time_after_last (time_is_start g t) (trace x)) as [[b mid]|]; [|exact I].
      rewrite existsb_app. cbn. rewrite orb_true_r. discriminate.
  - apply time_claims_snoc; [exact (ta_claims x Hx)|exact I].
Qed.

(** A sample command: the subscription becomes a sample that belongs to the same await
    as before, if any. *)
Lemma time_inva_issue_sample : forall x c n s',
  time_inva x -> waiter x = None ->
  (forall g t, time_sub_refs g t (Some s') = true -> time_sub_refs g t (sub x) = true) ->
  (forall g t, time_sub_refs g t (sub x) = true ->
     time_ldinv g t (set_sub (set_next_cmd (emit x (ACommand c KSample None)) n) (Some s'))) ->
  time_inva (set_sub (set_next_cmd (emit x (ACommand c KSample None)) n) (Some s')).
Proof.
  intros x c n s' Hx W0 Rs HL.
  set (a := ACommand c KSample None).
  assert (Ext : forall p, p a = false ->
     time_after_last p (trace x ++ [a]) =
     match time_after_last p (trace x) with Some (b, s) => Some (b, s ++ [a])
     | None => None end).
  { intros p Hp. rewrite time_after_last_snoc, Hp. reflexivity. }
  assert (St : forall g t, time_is_start g t a = false) by reflexivity.
  assert (Ow : forall g t, time_is_owned g t a = false) by reflexivity.
  constructor.
  - intros g t o I0. tsimp. apply time_existsb_app_true. exact (ta_r1 x Hx g t o I0).
  - intros g t I0. tsimp. apply time_existsb_app_true. exact (ta_r2 x Hx g t I0).
  - intros g t op E. tsimp. congruence.
  - intros g t R. tsimp. destruct (ta_r4 x Hx g t (Rs g t R)) as [[op0 [mid [M1 M2]]] Sc].
    unfold time_refd, time_since_credits in *. tsimp. split.
    + exists op0, (mid ++ [a]). rewrite Ext, M1 by apply St. split; [reflexivity|].
      apply time_existsb_app_true. exact M2.
    + rewrite Ext by apply Ow.
      destruct (time_after_last (time_is_owned g t) (trace x)) as [[b s]|]; [|exact I].
      rewrite time_credits_app, Sc. reflexivity.
  - intros g t O. tsimp. rewrite existsb_app, orb_false_r in O.
    apply time_existsb_app_true. exact (ta_owned x Hx g t O).
  - intros g t. destruct (time_sub_refs g t (sub x)) eqn:Rg; [exact (HL g t Rg)|].
    pose proof (ta_ld x Hx g t) as L. unfold time_ldinv in *. tsimp.
    rewrite Ext by apply St.
    destruct (time_after_last (time_is_start g t) (trace x)) as [[b mid]|]; [|exact I].
    destruct b; try exact I. intros Sl.
    apply (time_ld_away g t op mid _ x _ (L Sl)); tsimp; auto.
    + rewrite time_credits_app. cbn. apply app_nil_r.
    + destruct (time_sub_live g t (Some s')) eqn:E; [|reflexivity].
      assert (time_sub_refs g t (Some s') = true).
      { destruct s' as [|? []|]; cbn in E |- *; auto; discriminate. }
      rewrite (Rs g t H) in Rg. discriminate.
  - intros g t o I0. tsimp. pose proof (ta_p7 x Hx g t o I0) as H.
    unfold time_p7_ok in *. rewrite Ext by apply Ow.
    destruct (time_after_last (time_is_owned g t) (trace x)) as [[b s]|]; [|exact I].
    apply time_existsb_app_true. exact H.
  - intros g t I0. tsimp. destruct (ta_p8 x Hx g t I0) as [Ha Hb].
    unfold time_p8a_ok, time_p8b_ok in *. split.
    + rewrite Ext by apply Ow.
      destruct (time_after_last (time_is_owned g t) (trace x)) as [[b s]|]; [|exact I].
      destruct Ha as [Ha1 Ha2]. split; [apply time_existsb_app_true; exact Ha1|].
      rewrite time_credits_app, Ha2. reflexivity.
    + rewrite Ext by apply St.
      destruct (time_after_last (time_is_start g t) (trace x)) as [[b mid]|]; [|exact I].
      rewrite existsb_app. cbn. rewrite orb_true_r. discriminate.
  - tsimp. apply time_claims_snoc; [exact (ta_claims x Hx)|exact I].
Qed.

(** ** What the subscription tells of its await *)

Lemma time_ld_flink : forall f tok op mid x c k rest,
  time_ld f tok op mid x -> sub x = Some (SSample c (FLink f tok k rest)) ->
  waiter x = None -> phase x <> PDone ->
  1 <= k <= max_chunk /\ time_chain_ok op (credits f tok mid) k rest /\
  time_bounds (credits f tok mid).
Proof.
  intros f tok op mid x c k rest [B St] S W P.
  destruct St as [PD|[[S1 _]|[S2|[S3|[[_ [Lv _]]|[_ [Lv _]]]]]]].
  - contradiction.
  - congruence.
  - destruct S2 as [c' [d [k' [rest' [E _]]]]]. congruence.
  - destruct S3 as [c' [k' [rest' [E [K [Ch _]]]]]]. rewrite S in E. inversion E; subst. auto.
  - rewrite S in Lv. cbn in Lv. rewrite !Nat.eqb_refl in Lv. discriminate.
  - rewrite S in Lv. cbn in Lv. rewrite !Nat.eqb_refl in Lv. discriminate.
Qed.

Lemma time_ld_sop : forall f tok op mid x c op' k rest,
  time_ld f tok op mid x -> sub x = Some (SOp c f tok op' k rest) ->
  waiter x = None -> phase x <> PDone ->
  (exists d, op' = OSleep d) /\ 1 <= k <= max_chunk /\
  time_chain_ok op (credits f tok mid) k rest /\ time_nodel f tok (queue x).
Proof.
  intros f tok op mid x c op' k rest [B St] S W P.
  destruct St as [PD|[[S1 _]|[S2|[S3|[[_ [Lv _]]|[_ [Lv _]]]]]]].
  - contradiction.
  - congruence.
  - destruct S2 as [c' [d [k' [rest' [E [K [Ch N]]]]]]]. rewrite S in E. inversion E; subst.
    split; [eauto|auto].
  - destruct S3 as [c' [k' [rest' [E _]]]]. congruence.
  - rewrite S in Lv. cbn in Lv. rewrite !Nat.eqb_refl in Lv. discriminate.
  - rewrite S in Lv. cbn in Lv. rewrite !Nat.eqb_refl in Lv. discriminate.
Qed.

Lemma time_ld_fresult : forall f tok op mid x c o,
  time_ld f tok op mid x -> sub x = Some (SSample c (FResult f tok o)) ->
  waiter x = None -> phase x <> PDone -> False.
Proof.
  intros f tok op mid x c o [B St] S W P.
  destruct St as [PD|[[S1 _]|[S2|[S3|[[_ [Lv _]]|[_ [Lv _]]]]]]].
  - contradiction.
  - congruence.
  - destruct S2 as [c' [d [k' [rest' [E _]]]]]. congruence.
  - destruct S3 as [c' [k' [rest' [E _]]]]. congruence.
  - rewrite S in Lv. cbn in Lv. rewrite !Nat.eqb_refl in Lv. discriminate.
  - rewrite S in Lv. cbn in Lv. rewrite !Nat.eqb_refl in Lv. discriminate.
Qed.

(** ** An applied sample *)

Definition time_credit (after : Follows) : option (FiberId * Token * Z) :=
  match after with
  | FLink f tok k _ => if 0 <? k then Some (f, tok, k) else None
  | _ => None
  end.

Lemma time_inva_applied : forall x c v l after,
  time_inva x -> queue x = [] -> waiter x = None -> phase x <> PDone ->
  sub x = Some (SSample c after) ->
  time_inva (set_sub (set_logical (emit x (ASampled c v l (time_credit after))) l) None).
Proof.
  intros x c v l after Hx Q W P S.
  set (a := ASampled c v l (time_credit after)).
  assert (Ext : forall p, p a = false ->
     time_after_last p (trace x ++ [a]) =
     match time_after_last p (trace x) with Some (b, s) => Some (b, s ++ [a])
     | None => None end).
  { intros p Hp. rewrite time_after_last_snoc, Hp. reflexivity. }
  constructor; tsimp.
  - intros g t o I0. rewrite Q in I0. destruct I0.
  - intros g t I0. rewrite Q in I0. destruct I0.
  - intros g t op E. congruence.
  - intros g t R. discriminate.
  - intros g t O. rewrite existsb_app, orb_false_r in O.
    apply time_existsb_app_true. exact (ta_owned x Hx g t O).
  - intros g t. pose proof (ta_ld x Hx g t) as L. unfold time_ldinv in *. tsimp.
    rewrite Ext by reflexivity.
    destruct (time_after_last (time_is_start g t) (trace x)) as [[b mid]|] eqn:E;
      [|exact I].
    destruct b; try exact I. intros Sl. specialize (L Sl).
    destruct (time_after_last_start_some _ _ _ _ _ E) as [op1 Eo]. inversion Eo; subst.
    split.
    + rewrite time_credits_app. unfold time_bounds. apply Forall_app.
      split; [exact (proj1 L)|]. subst a. unfold credits. cbn.
      destruct after as [|? ? ?|f tok k rest|? ?|? ? ?]; cbn; try constructor.
      destruct (0 <? k); cbn; [|constructor].
      destruct (Nat.eqb g f) eqn:E1, (Nat.eqb t tok) eqn:E2; cbn; [|constructor..].
      apply Nat.eqb_eq in E1, E2. subst.
      destruct (time_ld_flink f tok op1 mid x c k rest L S W P) as [K _].
      constructor; [exact K|constructor].
    + right; right; right; right; right. tsimp. rewrite Q, W.
      split; [intros o I0; destruct I0|]. split; reflexivity.
  - intros g t o I0. rewrite Q in I0. destruct I0.
  - intros g t I0. rewrite Q in I0. destruct I0.
  - apply time_claims_snoc; [exact (ta_claims x Hx)|exact I].
Qed.
