(** * Step domain: an invariant of every state the executor reaches.

    [Inv] says what holds of [violated], the trace, [sub], [waiter] and [queue] in every state
    reached from an attempt's start, for any runtime. [IInv] is the weaker form that holds
    between the events of one task, while the queue may be anything. Each operation of the
    executor gets a preservation lemma, and [step_inv_reachable] closes the induction. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Statements.
Import ListNotations.
Open Scope Z_scope.

(** A sample issued for a fiber's result, link or cancellation: one the fiber still waits on. *)
Definition active (s : option Sub) : bool :=
  match s with
  | Some (SSample _ (FResult _ _ _)) | Some (SSample _ (FLink _ _ _ _))
  | Some (SSample _ (FCancelled _ _)) => true
  | _ => false
  end.

Definition released_sample (s : option Sub) : bool :=
  match s with Some (SSample _ (FReleased _ _ _)) => true | _ => false end.

Definition is_init (s : option Sub) : bool :=
  match s with Some (SSample _ FInitial) => true | _ => false end.

(** An action that is neither a violation nor an exit. *)
Definition plain_action (a : Action) : bool :=
  match a with AViolation _ | AExit _ => false | _ => true end.

Record Inv (x : XState) : Prop := {
  inv_viol : violated x = true -> phase x <> POpen;
  inv_vtrace : forall v, In (AViolation v) (trace x) -> violated x = true;
  inv_exit_done : forall w, In (AExit w) (trace x) -> phase x = PDone;
  inv_exit_defect : forall w v, In (AExit w) (trace x) -> In (AViolation v) (trace x) ->
                    w = VDefect;
  inv_cmd : forall sb, sub x = Some sb -> S (sub_cmd sb) = next_cmd x;
  inv_waiter : (waiter x <> None -> slot_held x = true \/ (sub x = None /\ queue x = [])) /\
               (is_init (sub x) = true -> queue x = [] /\ waiter x = None);
  inv_active : active (sub x) = true -> queue x = [];
  inv_released : released_sample (sub x) = false
}.

(** Between the events of a task: no awaited or initial sample is subscribed, and a waiter
    waits for a held slot. *)
Definition settled (x : XState) : Prop :=
  active (sub x) = false /\ is_init (sub x) = false /\ (waiter x <> None -> slot_held x = true).

Definition IInv (x : XState) : Prop := Inv x /\ settled x.

(** ** Field lemmas *)

Ltac fields := cbn [phase queue sub awaiter waiter held logical next_cmd cursor draws live
  root_exit violated trace progress micro fseen set_phase set_queue set_sub set_awaiter
  set_waiter set_held set_logical set_next_cmd set_cursor set_draws set_live set_root_exit
  set_violated set_progress set_micro set_fseen emit enqueue mk] in *.

(** An operation that leaves every field [Inv] reads unchanged keeps it. *)
Lemma step_inv_same : forall x y,
  violated y = violated x -> trace y = trace x -> phase y = phase x -> sub y = sub x ->
  next_cmd y = next_cmd x -> waiter y = waiter x -> queue y = queue x -> Inv x -> Inv y.
Proof.
  intros x y Hv Ht Hp Hs Hn Hw Hq [A B C D E F G J].
  assert (Hsl : slot_held y = slot_held x) by (unfold slot_held; rewrite Hs; reflexivity).
  constructor; rewrite ?Hv, ?Ht, ?Hp, ?Hs, ?Hn, ?Hw, ?Hq, ?Hsl; auto.
Qed.

Lemma step_settled_same : forall x y, sub y = sub x -> waiter y = waiter x ->
  settled x -> settled y.
Proof.
  intros x y Hs Hw [A [B C]].
  assert (Hsl : slot_held y = slot_held x) by (unfold slot_held; rewrite Hs; reflexivity).
  unfold settled; rewrite Hs, Hw, Hsl; auto.
Qed.

Lemma step_inv_set_progress : forall x v, Inv x -> Inv (set_progress x v).
Proof. intros x v H; apply (step_inv_same x); auto. Qed.
Lemma step_inv_set_micro : forall x v, Inv x -> Inv (set_micro x v).
Proof. intros x v H; apply (step_inv_same x); auto. Qed.
Lemma step_inv_set_fseen : forall x v, Inv x -> Inv (set_fseen x v).
Proof. intros x v H; apply (step_inv_same x); auto. Qed.
Lemma step_inv_set_cursor : forall x v, Inv x -> Inv (set_cursor x v).
Proof. intros x v H; apply (step_inv_same x); auto. Qed.
Lemma step_inv_set_live : forall x v, Inv x -> Inv (set_live x v).
Proof. intros x v H; apply (step_inv_same x); auto. Qed.
Lemma step_inv_set_draws : forall x v, Inv x -> Inv (set_draws x v).
Proof. intros x v H; apply (step_inv_same x); auto. Qed.
Lemma step_inv_set_awaiter : forall x v, Inv x -> Inv (set_awaiter x v).
Proof. intros x v H; apply (step_inv_same x); auto. Qed.
Lemma step_inv_set_held : forall x v, Inv x -> Inv (set_held x v).
Proof. intros x v H; apply (step_inv_same x); auto. Qed.

Lemma step_inv_set_waiter_none : forall x, Inv x -> Inv (set_waiter x None).
Proof.
  intros x [A B C D E [F1 F2] G J]; constructor; fields; auto.
  split; [congruence | intros H; destruct (F2 H); auto].
Qed.

Lemma step_inv_set_waiter_slot : forall x w, slot_held x = true -> is_init (sub x) = false ->
  Inv x -> Inv (set_waiter x (Some w)).
Proof.
  intros x w Hs Hi [A B C D E [F1 F2] G J]; constructor; fields; auto.
  split; [intros _; left; exact Hs | intros H; congruence].
Qed.
Lemma step_inv_set_root_exit : forall x v, Inv x -> Inv (set_root_exit x v).
Proof. intros x v H; apply (step_inv_same x); auto. Qed.
Lemma step_inv_set_logical : forall x v, Inv x -> Inv (set_logical x v).
Proof. intros x v H; apply (step_inv_same x); auto. Qed.

Lemma step_in_snoc : forall {X} (a b : X) l, In a (l ++ [b]) -> In a l \/ a = b.
Proof.
  intros X a b l H; apply in_app_or in H; destruct H as [H | [H | []]]; auto.
Qed.

Lemma step_inv_emit : forall x a, plain_action a = true -> Inv x -> Inv (emit x a).
Proof.
  intros x a Ha [A B C D E F G J]; constructor; fields; auto.
  - intros v H; apply step_in_snoc in H; destruct H as [H | H]; eauto; subst; discriminate.
  - intros w H; apply step_in_snoc in H; destruct H as [H | H]; eauto; subst; discriminate.
  - intros w v H1 H2; apply step_in_snoc in H1; apply step_in_snoc in H2.
    destruct H1 as [H1 | H1]; [| subst; discriminate].
    destruct H2 as [H2 | H2]; [| subst; discriminate]. eauto.
Qed.

Lemma step_inv_set_queue : forall x q, settled x -> Inv x -> Inv (set_queue x q).
Proof.
  intros x q [Ha [Hi Hw]] [A B C D E F G J]; constructor; fields; auto.
  - split; [intros H; left; auto | intros H; congruence].
  - intros H; rewrite H in Ha; discriminate.
Qed.

Lemma step_inv_enqueue : forall x t, settled x -> Inv x -> Inv (enqueue x t).
Proof. intros; apply step_inv_set_queue; auto. Qed.

Lemma step_inv_set_sub_none : forall x, queue x = [] -> Inv x -> Inv (set_sub x None).
Proof.
  intros x Q [A B C D E F G J]; constructor; fields; auto; try discriminate.
  split; [intros _; right; auto | discriminate].
Qed.

Lemma step_inv_set_held_false : forall x, Inv x -> Inv (set_held x false).
Proof. intros; apply step_inv_set_held; auto. Qed.

(** ** Closing, violations and the exit *)

Lemma step_close_phase : forall x c, phase x <> POpen -> phase (close x c) <> POpen.
Proof.
  intros x c H; unfold close; destruct (phase x) as [| [k |] |] eqn:E; try congruence;
    destruct c; fields; try congruence; discriminate.
Qed.

Lemma step_close_open : forall x c, phase x = POpen -> phase (close x c) = PClosing c.
Proof. intros x c H; unfold close; rewrite H; reflexivity. Qed.

Lemma step_close_trace : forall x c, trace (close x c) = trace x.
Proof.
  intros x c; unfold close; destruct (phase x) as [| [k |] |]; try destruct c; reflexivity.
Qed.

Lemma step_close_violated : forall x c, violated (close x c) = violated x.
Proof.
  intros x c; unfold close; destruct (phase x) as [| [k |] |]; try destruct c; reflexivity.
Qed.

Lemma step_inv_close : forall x c, Inv x -> Inv (close x c).
Proof.
  intros x c HI; pose proof HI as [A B C D E F G J].
  unfold close; destruct (phase x) eqn:P.
  - constructor; fields; rewrite ?P; auto; try discriminate.
    + intros w H; specialize (C w H); congruence.
    + split; intros H; [congruence | discriminate].
  - destruct cut as [k |]; [exact HI |].
    destruct c; [| exact HI].
    constructor; fields; rewrite ?P; auto; try discriminate.
    intros w H; specialize (C w H); congruence.
  - exact HI.
Qed.

Lemma step_inv_violate : forall x v, phase x <> PDone -> Inv x -> Inv (violate x v).
Proof.
  intros x v P HI; pose proof HI as [A B C D E F G J].
  unfold violate; destruct (violated x) eqn:V; [exact HI |].
  unfold close; fields; destruct (phase x) eqn:Q; [| destruct cut |]; try congruence;
    constructor; fields; rewrite ?Q; auto; try discriminate;
    try (intros w H; apply step_in_snoc in H; destruct H as [H | H];
         [specialize (C w H); congruence | discriminate]);
    try (intros w u H; apply step_in_snoc in H; destruct H as [H | H];
         [specialize (C w H); congruence | discriminate]);
    split; intros H; [congruence | discriminate].
Qed.

Lemma step_violate_phase : forall x v, phase x <> POpen -> phase (violate x v) <> POpen.
Proof.
  intros x v H; unfold violate; destruct (violated x); auto.
  apply step_close_phase; fields; auto.
Qed.

Lemma step_violate_open : forall x v, phase x = POpen -> violated x = false ->
  phase (violate x v) = PClosing None /\ trace (violate x v) = trace x ++ [AViolation v].
Proof.
  intros x v P V; unfold violate; rewrite V; split.
  - apply step_close_open; fields; auto.
  - rewrite step_close_trace; reflexivity.
Qed.

(** No violation is in the trace of an open state. *)
Lemma step_open_no_violation : forall x v, Inv x -> phase x = POpen ->
  ~ In (AViolation v) (trace x).
Proof.
  intros x v [A B C D E F G J] P H; apply B in H; apply A in H; auto.
Qed.

Lemma step_inv_finish : forall x w, Inv x ->
  (forall v, In (AViolation v) (trace x) -> w = VDefect) -> Inv (finish x w).
Proof.
  intros x w [A B C D E F G J] Hw; unfold finish; constructor; fields; auto;
    try discriminate.
  - intros v H; apply step_in_snoc in H; destruct H as [H | H]; eauto; discriminate.
  - intros w' v H1 H2; apply step_in_snoc in H2; destruct H2 as [H2 | H2]; [| discriminate].
    apply step_in_snoc in H1; destruct H1 as [H1 | H1]; eauto.
    inversion H1; subst; eauto.
Qed.

Lemma step_inv_finish_verdict : forall x, Inv x -> Inv (finish x (verdict x)).
Proof.
  intros x HI; apply step_inv_finish; auto.
  intros v H; apply (inv_vtrace _ HI) in H; unfold verdict; rewrite H; reflexivity.
Qed.

(** ** Issuing *)

Lemma step_inv_issue : forall I x k o s, Inv x -> phase x = POpen ->
  sub_cmd (s (next_cmd x)) = next_cmd x -> waiter x = None ->
  (active (Some (s (next_cmd x))) = true \/ is_init (Some (s (next_cmd x))) = true ->
   queue x = []) ->
  released_sample (Some (s (next_cmd x))) = false ->
  Inv (issue I x k o s).
Proof.
  intros I x k o s HI P Hc Hw Ha Hr.
  assert (Hgo : Inv (set_sub (set_next_cmd (emit x (ACommand (next_cmd x) k o))
                     (S (next_cmd x))) (Some (s (next_cmd x))))).
  { destruct HI as [A B C D E F G J]; constructor; fields; auto.
    - intros v H; apply step_in_snoc in H; destruct H as [H | H]; eauto; discriminate.
    - intros w H; apply step_in_snoc in H; destruct H as [H | H]; eauto; discriminate.
    - intros w v H1 H2; apply step_in_snoc in H1; apply step_in_snoc in H2.
      destruct H1 as [H1 | H1]; [| discriminate].
      destruct H2 as [H2 | H2]; [| discriminate]. eauto.
    - intros sb H; inversion H; subst; rewrite Hc; reflexivity. }
  unfold issue; cbv zeta; destruct (nth_error (persisted I) (next_cmd x)); [| exact Hgo].
  destruct (cmd_eqb k c); [exact Hgo |].
  apply step_inv_finish; auto.
  intros v H; exfalso; exact (step_open_no_violation x v HI P H).
Qed.

Lemma step_issue_phase : forall I x k o s, phase x <> POpen ->
  phase (issue I x k o s) <> POpen.
Proof.
  intros I x k o s H; unfold issue; cbv zeta.
  destruct (nth_error (persisted I) (next_cmd x)); [destruct (cmd_eqb k c) |];
    fields; auto; discriminate.
Qed.

Lemma step_inv_issue_sample : forall I x a, Inv x -> phase x = POpen -> waiter x = None ->
  (active (Some (SSample 0 a)) = true \/ is_init (Some (SSample 0 a)) = true -> queue x = []) ->
  released_sample (Some (SSample 0 a)) = false ->
  Inv (issue_sample I x a).
Proof.
  intros I x a HI P Hw Ha Hr; unfold issue_sample; apply step_inv_issue; auto;
    destruct a; auto.
Qed.

Lemma step_inv_issue_op : forall I x f tok op, Inv x -> phase x = POpen -> waiter x = None ->
  Inv (issue_op I x f tok op).
Proof.
  intros I x f tok op HI P Hw; unfold issue_op; destruct op as [k a | d].
  - apply step_inv_issue; auto; intros [H | H]; discriminate.
  - destruct (match d with Millis m => split m | Forever => (max_chunk, Endless) end).
    apply step_inv_issue; auto; intros [H | H]; discriminate.
Qed.

Lemma step_issue_op_active : forall I x f tok op, active (sub x) = false ->
  active (sub (issue_op I x f tok op)) = false.
Proof.
  intros I x f tok op H; unfold issue_op, issue; destruct op as [k a | d].
  - cbv zeta; destruct (nth_error (persisted I) (next_cmd x)); [destruct cmd_eqb |]; fields; auto.
  - destruct (match d with Millis m => split m | Forever => (max_chunk, Endless) end).
    cbv zeta; destruct (nth_error (persisted I) (next_cmd x)); [destruct cmd_eqb |]; fields; auto.
Qed.

Lemma step_close_active : forall x c, active (sub x) = false -> active (sub (close x c)) = false.
Proof.
  intros x c H; unfold close; destruct (phase x) as [| [k |] |]; try destruct c; auto.
Qed.

Lemma step_violate_active : forall x v, active (sub x) = false ->
  active (sub (violate x v)) = false.
Proof.
  intros x v H; unfold violate; destruct (violated x); auto; apply step_close_active; auto.
Qed.

Lemma step_close_settled : forall x c, settled x -> settled (close x c).
Proof.
  intros x c H; unfold close; destruct (phase x) as [| [k |] |]; try destruct c; auto.
  all: unfold settled, slot_held; fields; repeat split; try reflexivity; intros N; congruence.
Qed.

Lemma step_violate_settled : forall x v, settled x -> settled (violate x v).
Proof.
  intros x v H; unfold violate; destruct (violated x); auto; apply step_close_settled; auto.
Qed.

Lemma step_issue_op_settled : forall I x f tok op, waiter x = None -> settled x ->
  settled (issue_op I x f tok op).
Proof.
  intros I x f tok op Hw H; unfold issue_op, issue; destruct op as [k a | d];
    [| destruct (match d with Millis m => split m | Forever => (max_chunk, Endless) end)];
    cbv zeta; destruct (nth_error (persisted I) (next_cmd x));
    try (match goal with |- context [cmd_eqb ?a ?b] => destruct (cmd_eqb a b) end);
    unfold settled, slot_held in *; fields; rewrite ?Hw; auto;
    repeat split; try reflexivity; intros N; congruence.
Qed.

(** ** Inside a task *)

Lemma step_iinv_emit : forall x a, plain_action a = true -> IInv x -> IInv (emit x a).
Proof. intros x a Ha [H1 H2]; split; [apply step_inv_emit |]; auto. Qed.

Lemma step_iinv_enqueue : forall x t, IInv x -> IInv (enqueue x t).
Proof. intros x t [H1 H2]; split; [apply step_inv_enqueue |]; auto. Qed.

Lemma step_iinv_violate : forall x v, phase x <> PDone -> IInv x -> IInv (violate x v).
Proof.
  intros x v P [H1 H2]; split; [apply step_inv_violate | apply step_violate_settled]; auto.
Qed.

Lemma step_iinv_close : forall x c, IInv x -> IInv (close x c).
Proof. intros x c [H1 H2]; split; [apply step_inv_close | apply step_close_settled]; auto. Qed.

Lemma step_on_start_iinv : forall I x f tok op, IInv x -> IInv (on_start I x f tok op).
Proof.
  intros I x f tok op HI; unfold on_start; destruct (phase x) eqn:P.
  - cbv zeta.
    assert (HE : IInv (emit x (AStart f tok op))) by (apply step_iinv_emit; auto).
    destruct (zero_sleep op); [apply step_iinv_enqueue; auto |].
    destruct (awaiter (emit x (AStart f tok op))).
    + apply step_iinv_violate; auto; fields; congruence.
    + destruct HE as [HE1 HE2].
      destruct (held (emit x (AStart f tok op))) eqn:H.
      * split; [apply step_inv_enqueue; [| apply step_inv_set_held_false,
          step_inv_set_awaiter]|]; fields; auto.
      * destruct (slot_held _) eqn:Hsl.
        -- split; [apply step_inv_set_waiter_slot; [| | apply step_inv_set_awaiter] |];
             fields; auto; try apply HE2.
           unfold settled in *; fields; repeat split; try apply HE2; auto.
        -- assert (Hw : waiter (set_awaiter (emit x (AStart f tok op)) (Some (f, tok))) = None).
           { fields; destruct (waiter x) eqn:W; auto.
             destruct HE2 as [_ [_ HW]]; fields; rewrite W in HW.
             unfold slot_held in Hsl, HW; fields; rewrite HW in Hsl; [discriminate | congruence]. }
           split; [apply step_inv_issue_op; [apply step_inv_set_awaiter | |] |
                   apply step_issue_op_settled]; fields; auto.
  - apply step_iinv_enqueue, step_iinv_emit; auto.
  - exact HI.
Qed.

Lemma step_release_sub_cases : forall s f tok s', release_sub s = Some (f, tok, s') ->
  active (Some s) = false -> exists c f0 tok0 op k rest,
  s = SOp c f0 tok0 op k rest /\ s' = SReleased c.
Proof.
  intros s f tok s' H A; destruct s as [c f0 tok0 op k rest | c after | c].
  - inversion H; subst; eauto 10.
  - destruct after; discriminate.
  - discriminate.
Qed.

(** [on_release] in two parts: the queue filter, which may hold the cancellation again, and
    the rest. *)
Definition dropped_cancel (x : XState) (f : FiberId) (tok : Token) : bool :=
  existsb (fun t => match t with
                    | DeliverCancel f' tok' => Nat.eqb f f' && Nat.eqb tok tok'
                    | _ => false end) (queue x).

Definition release_pre (x : XState) (f : FiberId) (tok : Token) : XState :=
  match phase x with
  | POpen =>
      let x1 := set_queue x (filter (fun t => negb (for_token f tok t)) (queue x)) in
      if dropped_cancel x f tok then set_held x1 true else x1
  | _ => x
  end.

Definition release_rest (x : XState) (f : FiberId) (tok : Token) : XState :=
  match phase x, awaiter x with
  | POpen, Some a =>
      if negb (pair_eqb a (f, tok)) then x
      else
        let x1 := set_awaiter x None in
        match waiter x with
        | Some _ => set_waiter x1 None
        | None =>
            match sub x with
            | Some s => match release_sub s with
                        | Some (f', tok', s') =>
                            if pair_eqb (f', tok') (f, tok) then set_sub x1 (Some s') else x1
                        | None => x1
                        end
            | None => x1
            end
        end
  | _, _ => x
  end.

Lemma step_on_release_split : forall x f tok,
  on_release x f tok = release_rest (release_pre x f tok) f tok.
Proof. reflexivity. Qed.

Lemma step_release_pre_fields : forall x f tok,
  phase (release_pre x f tok) = phase x /\ sub (release_pre x f tok) = sub x /\
  awaiter (release_pre x f tok) = awaiter x /\ waiter (release_pre x f tok) = waiter x /\
  trace (release_pre x f tok) = trace x /\ cursor (release_pre x f tok) = cursor x /\
  (forall t, In t (queue (release_pre x f tok)) -> In t (queue x)) /\
  (phase x <> POpen -> release_pre x f tok = x).
Proof.
  intros x f tok; unfold release_pre; destruct (phase x) eqn:P.
  - cbv zeta; destruct (dropped_cancel x f tok); fields; rewrite ?P;
      repeat split; auto; try congruence;
      intros t Ht; apply filter_In in Ht; tauto.
  - repeat split; auto.
  - repeat split; auto.
Qed.

Lemma step_release_pre_iinv : forall x f tok, IInv x -> IInv (release_pre x f tok).
Proof.
  intros x f tok [H1 H2]; unfold release_pre; destruct (phase x); try (split; auto; fail).
  cbv zeta; destruct (dropped_cancel x f tok); split;
    try apply step_inv_set_held; try apply step_inv_set_queue; auto.
Qed.

Lemma step_on_release_iinv : forall x f tok, IInv x -> IInv (on_release x f tok).
Proof.
  intros x f tok HI; rewrite step_on_release_split.
  pose proof (step_release_pre_iinv x f tok HI) as HY.
  generalize dependent (release_pre x f tok); intros y HY; clear HI.
  unfold release_rest.
  destruct (phase y); try exact HY.
  destruct (awaiter y); [| exact HY].
  destruct (negb _); [exact HY |].
  destruct HY as [HY1 HY2].
  assert (HA : IInv (set_awaiter y None)).
  { split; [apply step_inv_set_awaiter |]; fields; auto. }
  cbv zeta; destruct (waiter y) eqn:W.
  - split; [apply step_inv_set_waiter_none, step_inv_set_awaiter; auto |].
    unfold settled in *; fields; destruct HY2 as [? [? ?]]; repeat split; auto; congruence.
  - destruct (sub y) as [s |] eqn:Hsub; [| exact HA].
    destruct (release_sub s) as [[[f' tok'] s'] |] eqn:R; [| exact HA].
    destruct (pair_eqb _ _); [| exact HA].
    destruct HY2 as [Ha [Hi Hw]]; rewrite Hsub in Ha.
    destruct (step_release_sub_cases s f' tok' s' R Ha) as (c & f0 & tok0 & op & k & rest
      & -> & ->).
    pose proof HY1 as [A B C D E F G J].
    split; [constructor | ]; fields; auto; try discriminate.
    + intros sb Hsb; inversion Hsb; subst. apply (E _ Hsub).
    + rewrite W; split; intros N; [congruence | discriminate].
    + unfold settled, slot_held; fields; rewrite W; repeat split; auto; congruence.
Qed.

Lemma step_on_event_iinv : forall I x e, IInv x -> IInv (on_event I x e).
Proof.
  intros I x e HI; unfold on_event; destruct (phase x) eqn:P; [| | exact HI];
    destruct e as [f tok op | f tok | pr t | f | r].
  all: try (apply step_on_start_iinv; auto).
  all: try (apply step_on_release_iinv; auto).
  all: try (destruct (Nat.eqb pr 0); [apply step_iinv_enqueue; auto |
                                      apply step_iinv_violate; auto; congruence]).
  all: try (destruct HI as [H1 H2]; split; [apply step_inv_set_live |]; auto).
  all: destruct (root_exit x); [apply step_iinv_violate; auto; congruence |].
  all: apply step_iinv_close; destruct HI as [H1 H2]; split;
         [apply step_inv_set_root_exit |]; auto.
Qed.

Lemma step_iinv_set_draws : forall x v, IInv x -> IInv (set_draws x v).
Proof. intros x v [H1 H2]; split; [apply step_inv_set_draws |]; auto. Qed.

Lemma step_iinv_set_awaiter : forall x v, IInv x -> IInv (set_awaiter x v).
Proof. intros x v [H1 H2]; split; [apply step_inv_set_awaiter |]; auto. Qed.

Lemma step_interp_iinv : forall {X} I (s : Script X) x, IInv x -> IInv (fst (interp I x s)).
Proof.
  intros X I s; induction s as [r | e k IH | f k IH | f k IH | f k IH]; intros x HI; cbn.
  - exact HI.
  - apply IH, step_on_event_iinv; auto.
  - apply IH; destruct (phase x); auto; apply step_iinv_emit; auto.
  - apply IH; destruct (phase x); try exact HI; apply step_iinv_emit; try reflexivity;
      apply step_iinv_set_draws; exact HI.
  - apply IH.
    assert (H1 : IInv (match phase x with PDone => x | _ => emit x (ARegister f) end))
      by (destruct (phase x); auto; apply step_iinv_emit; auto).
    destruct H1 as [H1 H2]; split; [apply step_inv_set_live |]; auto.
Qed.

(** The state a task's script starts from. *)
Definition head_state (x : XState) (t : Task) (rest : list Task) : XState :=
  let x0 := set_progress (set_queue x rest) (S (progress x)) in
  let x1 := match task_action t with Some a => emit x0 a | None => x0 end in
  match t, awaiter x1 with
  | Deliver f tok _, Some a | DeliverCancel f tok, Some a =>
      if pair_eqb a (f, tok) then set_awaiter x1 None else x1
  | _, _ => x1
  end.

Lemma step_run_head_eq : forall R I x r t rest,
  run_head R I x r t rest = interp I (head_state x t rest) (run_task R r t).
Proof. reflexivity. Qed.

Lemma step_head_state_iinv : forall x t rest, Inv x -> queue x = t :: rest ->
  IInv (head_state x t rest).
Proof.
  intros x t rest HI Q.
  assert (HA : active (sub x) = false).
  { destruct (active (sub x)) eqn:E; auto. rewrite (inv_active _ HI E) in Q; discriminate. }
  assert (HS : settled x).
  { destruct (inv_waiter _ HI) as [W1 W2]; split; [exact HA | split].
    - destruct (is_init (sub x)) eqn:E; auto; destruct (W2 eq_refl); congruence.
    - intros W; destruct (W1 W) as [H | [_ H]]; [exact H | congruence]. }
  assert (H0 : IInv (set_progress (set_queue x rest) (S (progress x)))).
  { split; [apply step_inv_set_progress, step_inv_set_queue; auto |].
    apply (step_settled_same x); auto. }
  unfold head_state; cbv zeta.
  assert (H1 : IInv (match task_action t with Some a => emit (set_progress (set_queue x rest)
            (S (progress x))) a | None => set_progress (set_queue x rest) (S (progress x)) end)).
  { destruct t; cbn; auto; apply step_iinv_emit; auto. }
  revert H1; generalize (match task_action t with Some a => emit (set_progress (set_queue x rest)
            (S (progress x))) a | None => set_progress (set_queue x rest) (S (progress x)) end).
  intros y Hy; destruct t; auto; destruct (awaiter y); auto; destruct (pair_eqb _ _); auto;
    apply step_iinv_set_awaiter; auto.
Qed.

Lemma step_run_head_inv : forall R I x r t rest, Inv x -> queue x = t :: rest ->
  Inv (fst (run_head R I x r t rest)).
Proof.
  intros; rewrite step_run_head_eq; apply step_interp_iinv, step_head_state_iinv; auto.
Qed.

(** ** At a turn boundary *)

Lemma step_apply_sample_cases : forall x c s after,
  apply_sample x c s after = violate x Overflow \/
  exists a l, plain_action a = true /\
              apply_sample x c s after = set_sub (set_logical (emit x a) l) None.
Proof.
  intros; unfold apply_sample; cbv zeta; destruct (max_safe <? _); [left; reflexivity |].
  right; do 2 eexists; split; [| reflexivity]; reflexivity.
Qed.

(** The waiter is [None] when the subscription neither holds the slot nor is empty, or is
    the initial sample. *)
Lemma step_waiter_free : forall x, Inv x -> slot_held x = false -> sub x <> None ->
  waiter x = None.
Proof.
  intros x HI Hs Hn; destruct (waiter x) eqn:W; auto.
  destruct (proj1 (inv_waiter _ HI) ltac:(congruence)) as [H | [H _]]; congruence.
Qed.

Lemma step_waiter_init : forall x c, Inv x -> sub x = Some (SSample c FInitial) ->
  waiter x = None.
Proof.
  intros x c HI S0; apply (proj2 (inv_waiter _ HI)); rewrite S0; reflexivity.
Qed.

Lemma step_inv_after_sample : forall I y after, Inv y -> phase y = POpen -> sub y = None ->
  waiter y = None -> Inv (after_sample I y after).
Proof.
  intros I y after HI P S0 Hw.
  assert (HS : settled y) by (unfold settled; rewrite S0, Hw; repeat split; congruence).
  destruct after as [| f tok o | f tok k rest | f tok | f tok k];
    cbn; try (apply step_inv_enqueue; [exact HS | exact HI]); auto.
  destruct (link_of rest) as [[chunk rest'] |].
  - apply step_inv_issue; auto; try discriminate.
    intros [H | H]; discriminate.
  - apply step_inv_enqueue; [exact HS | exact HI].
Qed.

Lemma step_inv_notify_sample : forall I x c v after, Inv x -> phase x = POpen ->
  violated x = false -> queue x = [] -> waiter x = None ->
  Inv (let x1 := apply_sample x c v after in
       match phase x1 with POpen => after_sample I x1 after | _ => x1 end).
Proof.
  intros I x c v after HI P Hv Q Hw; cbv zeta.
  destruct (step_apply_sample_cases x c v after) as [E | (a & l & Ha & E)]; rewrite E.
  - destruct (step_violate_open x Overflow P Hv) as [Hp _]; rewrite Hp.
    apply step_inv_violate; [congruence | exact HI].
  - cbn [phase set_sub set_logical emit mk]; rewrite P.
    apply step_inv_after_sample; fields; auto.
    apply step_inv_set_sub_none; [fields; auto |].
    apply step_inv_set_logical, step_inv_emit; auto.
Qed.

Lemma step_inv_on_notify : forall I x s r, Inv x -> phase x = POpen -> queue x = [] ->
  sub x = Some s -> Inv (on_notify I x s r).
Proof.
  intros I x s r HI P Q S0.
  assert (Hv : violated x = false).
  { destruct (violated x) eqn:V; auto; exfalso; exact (inv_viol _ HI V P). }
  destruct s as [c f tok op k rest | c after | c]; unfold on_notify.
  - assert (Hw : waiter x = None)
      by (apply step_waiter_free; auto; [unfold slot_held; rewrite S0 |]; congruence).
    destruct op as [kk aa | d], r as [o | v |]; try exact HI;
      apply step_inv_issue_sample; auto; try discriminate; auto.
  - destruct r as [o | v |].
    + destruct after; try exact HI. apply step_inv_set_sub_none; auto.
    + destruct after as [| f tok o | f tok kk rest | f tok | f tok kk];
        try (apply step_inv_set_sub_none; auto; fail);
        apply step_inv_notify_sample; auto;
        [apply (step_waiter_init x c) |
         apply step_waiter_free; auto; [unfold slot_held; rewrite S0 |]; congruence ..];
        auto.
    + destruct after; try (apply step_inv_set_sub_none; auto);
        apply step_inv_violate; auto; congruence.
  - apply step_inv_set_sub_none; auto.
Qed.

Lemma step_inv_on_cancel : forall I x s, Inv x -> phase x = POpen -> queue x = [] ->
  sub x = Some s -> Inv (on_cancel I x s).
Proof.
  intros I x s HI P Q S0.
  assert (Hw : slot_held x = false -> waiter x = None)
    by (intros H; apply step_waiter_free; auto; congruence).
  destruct s as [c f tok op k rest | c after | c]; cbn.
  - apply step_inv_issue_sample; auto; try (apply Hw; unfold slot_held; rewrite S0; auto).
  - destruct after as [| f tok o | f tok kk rest | f tok | f tok kk].
    + apply step_inv_issue_sample; fields; auto.
      * apply step_inv_set_held; auto.
      * apply (step_waiter_init x c); auto.
    + apply step_inv_issue_sample; auto; try (apply Hw; unfold slot_held; rewrite S0; auto).
    + apply step_inv_issue_sample; auto; try (apply Hw; unfold slot_held; rewrite S0; auto).
    + apply step_inv_issue_sample; auto; try (apply Hw; unfold slot_held; rewrite S0; auto).
    + apply step_inv_set_held, step_inv_set_sub_none; auto.
  - apply step_inv_set_held, step_inv_set_sub_none; auto.
Qed.

Lemma step_inv_at_boundary_sub : forall I Sch x s y, Inv x -> phase x = POpen ->
  queue x = [] -> sub x = Some s -> at_boundary_sub I Sch x s = Some y -> Inv y.
Proof.
  intros I Sch x s y HI P Q S0 E; unfold at_boundary_sub in E.
  destruct (arrived Sch (micro x) <=? cursor x)%nat; [discriminate |].
  destruct (nth_error (entries I) (cursor x)) as [[c r |] |]; [| | discriminate].
  - destruct (Nat.eqb c (sub_cmd s)).
    + inversion E; subst; apply step_inv_on_notify; fields; auto.
      apply step_inv_set_cursor; auto.
    + destruct (c <? next_cmd x)%nat; inversion E; subst; apply step_inv_set_cursor; auto.
  - inversion E; subst; apply step_inv_on_cancel; fields; auto.
    apply step_inv_set_cursor; auto.
Qed.

Lemma step_inv_at_boundary : forall I Sch x y, Inv x -> queue x = [] ->
  at_boundary I Sch x = Some y -> Inv y.
Proof.
  intros I Sch x y HI Q E; unfold at_boundary in E.
  destruct (phase x) eqn:P; [| inversion E; subst; apply step_inv_finish_verdict; auto |
                               discriminate].
  destruct (held x) eqn:H, (waiter x) as [[[f tok] op] |] eqn:W.
  - inversion E; subst. apply step_inv_enqueue.
    + destruct (inv_waiter _ HI) as [W1 W2].
      unfold settled; fields; split; [| split; [| congruence]].
      * destruct (W1 ltac:(congruence)) as [Hs | [Hs _]];
          [unfold slot_held in Hs | rewrite Hs; reflexivity].
        destruct (sub x) as [[| c [] |] |]; auto; discriminate.
      * destruct (is_init (sub x)) eqn:Ei; auto; destruct (W2 eq_refl); congruence.
    + apply step_inv_set_waiter_none, step_inv_set_held_false; auto.
  - destruct (sub x) as [s |] eqn:S0; [eapply step_inv_at_boundary_sub; eauto |].
    inversion E; subst; apply step_inv_violate; auto; congruence.
  - destruct (sub x) as [s |] eqn:S0; [eapply step_inv_at_boundary_sub; eauto |].
    inversion E; subst; apply step_inv_issue_op; fields; auto.
    apply step_inv_set_waiter_none; auto.
  - destruct (sub x) as [s |] eqn:S0; [eapply step_inv_at_boundary_sub; eauto |].
    inversion E; subst; apply step_inv_violate; auto; congruence.
Qed.

(** ** One step, and reachable states *)

Lemma step_inv_set_phase_done : forall x, Inv x -> Inv (set_phase x PDone).
Proof.
  intros x [A B C D E F G J]; constructor; fields; auto; discriminate.
Qed.

Lemma step_inv_on_foreign : forall x fi, phase x <> PDone -> Inv x -> Inv (on_foreign x fi).
Proof.
  intros x fi P HI; destruct fi; cbn; auto; apply step_inv_violate; auto.
Qed.

Lemma step_inv_on_cut : forall x k, Inv x -> Inv (on_cut x k).
Proof.
  intros x k HI; unfold on_cut; destruct k;
    [apply step_inv_close | apply step_inv_close | apply step_inv_set_phase_done];
    apply step_inv_emit; auto.
Qed.

(** [step]'s shape: [next] applied to the new executor state. *)
Lemma step_xs : forall R I Sch s, xs (step R I Sch s) =
  match phase (xs s) with
  | PDone => xs s
  | _ =>
    if stop_due Sch (xs s) then set_micro (set_phase (xs s) PDone) (S (micro (xs s))) else
    match foreign_due I (xs s) with
    | Some fi => set_micro (on_foreign (set_fseen (xs s) (Some (progress (xs s)))) fi)
                   (S (micro (xs s)))
    | None =>
    match cut_due Sch (xs s) with
    | Some k => set_micro (on_cut (xs s) k) (S (micro (xs s)))
    | None =>
    match queue (xs s) with
    | t :: rest => set_micro (fst (run_head R I (xs s) (rs s) t rest)) (S (micro (xs s)))
    | [] => match at_boundary I Sch (xs s) with
            | Some x' => set_micro (set_progress x' (S (progress (xs s)))) (S (micro (xs s)))
            | None => set_micro (xs s) (S (micro (xs s)))
            end
    end
    end
    end
  end.
Proof.
  intros R I Sch s; unfold step; cbv beta zeta.
  destruct (phase (xs s)); try reflexivity;
    destruct (stop_due Sch (xs s)); try reflexivity;
    destruct (foreign_due I (xs s)); try reflexivity;
    destruct (cut_due Sch (xs s)); try reflexivity;
    destruct (queue (xs s)); try (destruct (at_boundary I Sch (xs s)); reflexivity);
    destruct (run_head R I (xs s) (rs s) t l); reflexivity.
Qed.

Lemma step_inv_step : forall R I Sch s, Inv (xs s) -> Inv (xs (step R I Sch s)).
Proof.
  intros R I Sch s HI; rewrite step_xs.
  destruct (phase (xs s)) eqn:P; try exact HI;
    (destruct (stop_due Sch (xs s)); [apply step_inv_set_micro, step_inv_set_phase_done; auto|]);
    (destruct (foreign_due I (xs s)) as [fi |];
       [apply step_inv_set_micro, step_inv_on_foreign; fields; [congruence |];
        apply step_inv_set_fseen; auto |]);
    (destruct (cut_due Sch (xs s)) as [k |];
       [apply step_inv_set_micro, step_inv_on_cut; auto |]);
    (destruct (queue (xs s)) as [| t rest] eqn:Q;
       [destruct (at_boundary I Sch (xs s)) eqn:E;
          [apply step_inv_set_micro, step_inv_set_progress; eapply step_inv_at_boundary; eauto
          | apply step_inv_set_micro; auto]
       | apply step_inv_set_micro, step_run_head_inv; auto]).
Qed.

Lemma step_inv_initial : forall R p I, Inv (xs (initial R p I)).
Proof.
  intros R p I; cbn [initial xs].
  apply step_inv_issue_sample; cbn; auto; try discriminate.
  constructor; cbn; intuition discriminate.
Qed.

Lemma step_inv_iterate : forall R I Sch n s, Inv (xs s) -> Inv (xs (iterate R I Sch n s)).
Proof.
  intros R I Sch n; induction n as [| n IH]; intros s HI; cbn; auto.
  apply IH, step_inv_step; auto.
Qed.

Theorem step_inv_reachable : forall R p I Sch s, reachable R p I Sch s -> Inv (xs s).
Proof.
  intros R p I Sch s [n ->]; apply step_inv_iterate, step_inv_initial.
Qed.
