(** * Facts about the executor's helpers, for the proofs of S8.

    What each helper does to the fields the time invariants read: the phase, the queue, the
    subscription, the awaiter and waiter, [L], the violation latch and the trace. Each step
    only appends to the trace, which is proved here first. *)

From Coq Require Import List ZArith Bool Arith Lia Sorting.
From Durable Require Import Runtime Exec Rev3 Statements TimeBase.
Import ListNotations.
Open Scope Z_scope.

(** Reduce the field updates and projections, and nothing else. *)
Ltac tsimp :=
  cbn [emit mk set_phase set_queue set_sub set_awaiter set_waiter set_held set_logical
       set_next_cmd set_cursor set_draws set_live set_root_exit set_violated set_progress
       set_micro set_fseen enqueue phase queue sub awaiter waiter held logical next_cmd
       cursor draws live root_exit violated trace progress micro fseen xs rs] in *.

(** ** The helpers *)

Lemma time_close_fields : forall x c,
  trace (close x c) = trace x /\ logical (close x c) = logical x /\
  violated (close x c) = violated x /\
  (phase x = POpen -> phase (close x c) = PClosing c /\ sub (close x c) = None /\
     waiter (close x c) = None /\ awaiter (close x c) = None /\
     queue (close x c) =
       map RequestInterrupt (live x) ++ filter (fun t => negb (is_delivery t)) (queue x)) /\
  (phase x <> POpen -> queue (close x c) = queue x /\ sub (close x c) = sub x /\
     waiter (close x c) = waiter x /\ awaiter (close x c) = awaiter x /\
     phase (close x c) <> POpen /\ (phase x = PDone -> phase (close x c) = PDone)).
Proof.
  intros x c. unfold close.
  destruct (phase x) as [|[k|]|] eqn:Ph; cbn; try (destruct c; cbn);
    repeat split; intros; try reflexivity; try congruence; rewrite ?Ph; try discriminate.
Qed.

(** A violation: the latch was already set and nothing changes, or it is recorded and the
    attempt closes. *)
Lemma time_violate_cases : forall x v,
  violate x v = x /\ violated x = true \/
  violated x = false /\
  violate x v = close (set_violated (emit x (AViolation v)) true) None.
Proof.
  intros x v. unfold violate. destruct (violated x); [left|right]; auto.
Qed.

Lemma time_violate_fields : forall x v,
  (violated x = true -> phase x <> POpen) ->
  violated (violate x v) = true /\ logical (violate x v) = logical x /\
  phase (violate x v) <> POpen /\
  (phase x = PDone -> phase (violate x v) = PDone) /\
  (trace (violate x v) = trace x \/ trace (violate x v) = trace x ++ [AViolation v]).
Proof.
  intros x v Hv. destruct (time_violate_cases x v) as [[-> H]|[H ->]].
  - repeat split; auto.
  - destruct (time_close_fields (set_violated (emit x (AViolation v)) true) None)
      as [T [L [V [Op Cl]]]].
    cbn in *. rewrite T, L, V. repeat split; auto.
    + destruct (phase x) eqn:Ph.
      * destruct (Op eq_refl) as [-> _]. discriminate.
      * apply Cl; discriminate.
      * apply Cl; discriminate.
    + intros Hd. apply Cl; [rewrite Hd; discriminate|]. exact Hd.
Qed.

Lemma time_issue_cases : forall I x k o s,
  issue I x k o s = finish x VMismatch \/
  issue I x k o s =
    set_sub (set_next_cmd (emit x (ACommand (next_cmd x) k o)) (S (next_cmd x)))
      (Some (s (next_cmd x))).
Proof.
  intros. unfold issue. destruct (nth_error (persisted I) (next_cmd x)) as [k'|].
  - destruct (cmd_eqb k k'); auto.
  - auto.
Qed.

Lemma time_issue_op_cases : forall I x f tok op,
  issue_op I x f tok op = finish x VMismatch \/
  exists k sb, issue_op I x f tok op =
    set_sub (set_next_cmd (emit x (ACommand (next_cmd x) k (Some (f, tok))))
      (S (next_cmd x))) (Some sb) /\
    match op with
    | ORun _ _ => sb = SOp (next_cmd x) f tok op 0 NoChain
    | OSleep d =>
        sb = SOp (next_cmd x) f tok op
          (fst match d with Millis m => split m | Forever => (max_chunk, Endless) end)
          (snd match d with Millis m => split m | Forever => (max_chunk, Endless) end)
    end.
Proof.
  intros. unfold issue_op. destruct op as [kd a|d].
  - destruct (time_issue_cases I x (KOp (ORun kd a)) (Some (f, tok))
      (fun c => SOp c f tok (ORun kd a) 0 NoChain)) as [H|H]; [left; exact H|].
    right. eexists _, _. split; [exact H|reflexivity].
  - destruct (match d with Millis m => split m | Forever => (max_chunk, Endless) end)
      as [ch rest] eqn:E.
    destruct (time_issue_cases I x (KOp (OSleep (Millis ch))) (Some (f, tok))
      (fun c => SOp c f tok (OSleep d) ch rest)) as [H|H]; [left; exact H|].
    right. eexists _, _. split; [exact H|]. reflexivity.
Qed.

(** ** Running a script *)

(** What [interp] does at a fiber's first run: record it, unless the attempt is done, and
    add it to the registry. *)
Definition time_reg (x : XState) (f : FiberId) : XState :=
  let x1 := match phase x with PDone => x | _ => emit x (ARegister f) end in
  set_live x1 (live x1 ++ [f]).

(** A property of states that each event and each answered question preserves holds after
    a whole script. *)
Lemma time_interp_ind : forall (P : XState -> Prop) I,
  (forall x e, P x -> P (on_event I x e)) ->
  (forall x f, P x -> P (match phase x with PDone => x | _ => emit x (AClock f (logical x)) end)) ->
  (forall x f, P x -> P (match phase x with
                         | PDone => x
                         | _ => emit (set_draws x (S (draws x))) (ADraw f (stream I (draws x)))
                         end)) ->
  (forall x f, P x -> P (time_reg x f)) ->
  forall X (s : Script X) x, P x -> P (fst (interp I x s)).
Proof.
  intros P I He Hc Hd Hr X s. induction s as [r|e k IH|f k IH|f k IH|f k IH];
    intros x Hx; cbn.
  - exact Hx.
  - apply IH. apply He. exact Hx.
  - apply IH. apply Hc. exact Hx.
  - apply IH. apply Hd. exact Hx.
  - apply IH. apply Hr. exact Hx.
Qed.

(** ** The trace only grows *)

Definition time_grows (x x' : XState) : Prop := exists r, trace x' = trace x ++ r.

Lemma time_grows_refl : forall x, time_grows x x.
Proof. intros x. exists []. rewrite app_nil_r. reflexivity. Qed.

Lemma time_grows_trans : forall x y z, time_grows x y -> time_grows y z -> time_grows x z.
Proof.
  intros x y z [r1 H1] [r2 H2]. exists (r1 ++ r2). rewrite H2, H1, app_assoc. reflexivity.
Qed.

Lemma time_grows_same : forall x x', trace x' = trace x -> time_grows x x'.
Proof. intros x x' H. exists []. rewrite H, app_nil_r. reflexivity. Qed.

Lemma time_grows_emit : forall x a, time_grows x (emit x a).
Proof. intros x a. exists [a]. reflexivity. Qed.

Lemma time_grows_close : forall x c, time_grows x (close x c).
Proof.
  intros x c. apply time_grows_same. apply (time_close_fields x c).
Qed.

Lemma time_grows_violate : forall x v, time_grows x (violate x v).
Proof.
  intros x v. unfold violate. destruct (violated x); [apply time_grows_refl|].
  eapply time_grows_trans; [apply (time_grows_emit x (AViolation v))|].
  eapply time_grows_trans; [|apply time_grows_close]. apply time_grows_same. reflexivity.
Qed.

Lemma time_grows_finish : forall x v, time_grows x (finish x v).
Proof. intros x v. exists [AExit v]. reflexivity. Qed.

Lemma time_grows_issue : forall I x k o s, time_grows x (issue I x k o s).
Proof.
  intros. destruct (time_issue_cases I x k o s) as [-> | ->].
  - apply time_grows_finish.
  - exists [ACommand (next_cmd x) k o]. reflexivity.
Qed.

Lemma time_grows_issue_op : forall I x f tok op, time_grows x (issue_op I x f tok op).
Proof.
  intros. unfold issue_op. destruct op; [apply time_grows_issue|].
  destruct (match d with Millis m => split m | Forever => (max_chunk, Endless) end).
  apply time_grows_issue.
Qed.

Lemma time_grows_on_start : forall I x f tok op, time_grows x (on_start I x f tok op).
Proof.
  intros. unfold on_start. destruct (phase x).
  - eapply time_grows_trans; [apply (time_grows_emit x (AStart f tok op))|].
    destruct (zero_sleep op); [apply time_grows_same; reflexivity|].
    destruct (awaiter (emit x (AStart f tok op))); [apply time_grows_violate|].
    destruct (held (emit x (AStart f tok op))); [apply time_grows_same; reflexivity|].
    destruct (slot_held (emit x (AStart f tok op))); [apply time_grows_same; reflexivity|].
    eapply time_grows_trans; [|apply time_grows_issue_op]. apply time_grows_same.
    reflexivity.
  - exists [AStart f tok op]. reflexivity.
  - apply time_grows_refl.
Qed.

Lemma time_grows_on_release : forall x f tok, time_grows x (on_release x f tok).
Proof.
  intros. apply time_grows_same. unfold on_release.
  repeat (cbn; match goal with |- context [match ?e with _ => _ end] => destruct e end);
    reflexivity.
Qed.

Lemma time_grows_on_event : forall I x e, time_grows x (on_event I x e).
Proof.
  intros. unfold on_event. destruct (phase x); try apply time_grows_refl;
  (destruct e as [f tok op|f tok|pr t|f|r];
   [apply time_grows_on_start|apply time_grows_on_release| |apply time_grows_same; reflexivity|];
   [destruct (Nat.eqb pr 0); [apply time_grows_same; reflexivity|apply time_grows_violate]
   |destruct (root_exit x); [apply time_grows_violate|]];
   eapply time_grows_trans; [|apply time_grows_close]; apply time_grows_same; reflexivity).
Qed.

Lemma time_grows_interp : forall I X (s : Script X) x, time_grows x (fst (interp I x s)).
Proof.
  intros I X s. induction s as [r|e k IH|f k IH|f k IH|f k IH]; intros x; cbn.
  - apply time_grows_refl.
  - eapply time_grows_trans; [apply time_grows_on_event|apply IH].
  - eapply time_grows_trans; [|apply IH].
    destruct (phase x); try apply time_grows_emit; apply time_grows_refl.
  - eapply time_grows_trans; [|apply IH].
    destruct (phase x); try (exists [ADraw f (stream I (draws x))]; reflexivity);
      apply time_grows_refl.
  - eapply time_grows_trans; [|apply IH].
    destruct (phase x); try (exists [ARegister f]; reflexivity);
      apply time_grows_same; reflexivity.
Qed.

Lemma time_nodup_grows : forall x x',
  time_grows x x' -> NoDup (time_stoks (trace x')) -> NoDup (time_stoks (trace x)).
Proof.
  intros x x' [r H] N. rewrite H in N. eapply time_nodup_prefix; exact N.
Qed.

(** A property each event and answer preserves, given that the final trace starts no token
    twice, holds after the whole script. *)
Lemma time_interp_ind_nodup : forall (P : XState -> Prop) I,
  (forall x e, P x -> NoDup (time_stoks (trace (on_event I x e))) -> P (on_event I x e)) ->
  (forall x f, P x -> P (match phase x with PDone => x | _ => emit x (AClock f (logical x)) end)) ->
  (forall x f, P x -> P (match phase x with
                         | PDone => x
                         | _ => emit (set_draws x (S (draws x))) (ADraw f (stream I (draws x)))
                         end)) ->
  (forall x f, P x -> P (time_reg x f)) ->
  forall X (s : Script X) x, P x -> NoDup (time_stoks (trace (fst (interp I x s)))) ->
    P (fst (interp I x s)).
Proof.
  intros P I He Hc Hd Hr X s. induction s as [r|e k IH|f k IH|f k IH|f k IH];
    intros x Hx N; cbn in *.
  - exact Hx.
  - apply IH; [|exact N]. apply He; [exact Hx|].
    eapply time_nodup_grows; [apply time_grows_interp|exact N].
  - apply IH; [apply Hc; exact Hx|exact N].
  - apply IH; [apply Hd; exact Hx|exact N].
  - apply IH; [apply Hr; exact Hx|exact N].
Qed.
