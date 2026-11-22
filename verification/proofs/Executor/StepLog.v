(** * Step domain: the runtime's log of an executor run.

    The interface properties I4, I6, I7 and I8 are stated about [drive]: a runtime given a
    list of tasks and a fixed table of answers. The executor instead runs one task at a time
    and answers each question from its own state. This file rebuilds the log the runtime sees
    during an executor run ([elog]) and the tasks the executor gave it ([etasks]), builds a
    table of answers from that log ([answers_of]), and proves that driving the runtime with
    those tasks and answers reproduces the log exactly ([step_drive_elog]). The one condition
    is that every registration was answered [false], which holds whenever the run is still
    open at its end, since a fiber is told to stop only during closing. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Statements StepInv StepTurn.
Import ListNotations.
Open Scope Z_scope.

(** ** The log of one task *)

(** The entries a script reports while [interp] runs it, with the executor's answers. *)
Fixpoint ilog {X} (I : Inputs) (x : XState) (s : Script X) : list LogEntry :=
  match s with
  | Done _ => []
  | Emit e k => LEvent e :: ilog I (on_event I x e) k
  | AskClock f k =>
      let l := logical x in
      let x1 := match phase x with PDone => x | _ => emit x (AClock f l) end in
      LClock f l :: ilog I x1 (k l)
  | AskDraw f k =>
      let r := stream I (draws x) in
      let x1 := match phase x with
                | PDone => x
                | _ => emit (set_draws x (S (draws x))) (ADraw f r)
                end in
      LDraw f r :: ilog I x1 (k r)
  | Register f k =>
      let closing := match phase x with PClosing _ => true | _ => false end in
      LRegister f closing :: ilog I (set_live x (live x ++ [f])) (k closing)
  end.

(** ** Answer tables *)

Definition clocks (L : list LogEntry) : list Z :=
  flat_map (fun e => match e with LClock _ l => [l] | _ => [] end) L.
Definition draw_values (L : list LogEntry) : list nat :=
  flat_map (fun e => match e with LDraw _ r => [r] | _ => [] end) L.

(** [A] gives, from read counters [c] and [d], exactly the answers [L] records. *)
Fixpoint answers_ok (A : Answers) (c d : nat) (L : list LogEntry) : Prop :=
  match L with
  | [] => True
  | LClock _ l :: rest => clock_answer A c = l /\ answers_ok A (S c) d rest
  | LDraw _ r :: rest => draw_answer A d = r /\ answers_ok A c (S d) rest
  | LRegister f b :: rest => register_answer A f = b /\ answers_ok A c d rest
  | _ :: rest => answers_ok A c d rest
  end.

Lemma step_answers_ok_app : forall A L1 L2 c d,
  answers_ok A c d (L1 ++ L2) ->
  answers_ok A c d L1 /\
  answers_ok A (c + length (clocks L1))%nat (d + length (draw_values L1))%nat L2.
Proof.
  intros A L1; induction L1 as [| e L1 IH]; intros L2 c d H; cbn in *.
  - rewrite !Nat.add_0_r; auto.
  - destruct e as [t | ev | f l | f r | f b]; cbn in *.
    + destruct (IH L2 c d H); auto.
    + destruct (IH L2 c d H); auto.
    + destruct H as [H1 H2]; destruct (IH L2 (S c) d H2) as [H3 H4].
      rewrite Nat.add_succ_r; auto.
    + destruct H as [H1 H2]; destruct (IH L2 c (S d) H2) as [H3 H4].
      rewrite Nat.add_succ_r; auto.
    + destruct H as [H1 H2]; destruct (IH L2 c d H2); auto.
Qed.

(** Running a script against answers that agree with the executor's gives the executor's log,
    its result, and the counters advanced by the reads in the log. *)
Lemma step_play_ilog : forall {X} I (s : Script X) x A c d,
  answers_ok A c d (ilog I x s) ->
  play A c d s = (ilog I x s, snd (interp I x s),
                  (c + length (clocks (ilog I x s)))%nat,
                  (d + length (draw_values (ilog I x s)))%nat).
Proof.
  intros X I s; induction s as [r | e k IH | f k IH | f k IH | f k IH];
    intros x A c d H; cbn in *.
  - rewrite !Nat.add_0_r; reflexivity.
  - rewrite (IH _ _ _ _ H); reflexivity.
  - destruct H as [H1 H2]; rewrite H1, (IH _ _ _ _ _ H2), Nat.add_succ_r; reflexivity.
  - destruct H as [H1 H2]; rewrite H1, (IH _ _ _ _ _ H2), Nat.add_succ_r; reflexivity.
  - destruct H as [H1 H2]; rewrite H1, (IH _ _ _ _ _ H2); reflexivity.
Qed.

(** ** The log of a run *)

Definition step_log (R : Runtime) (I : Inputs) (Sch : Schedule) (s : Sys R)
    : list LogEntry * list Task :=
  match phase (xs s) with
  | PDone => ([], [])
  | _ =>
    if stop_due Sch (xs s) then ([], []) else
    match foreign_due I (xs s) with
    | Some _ => ([], [])
    | None =>
    match cut_due Sch (xs s) with
    | Some _ => ([], [])
    | None =>
    match queue (xs s) with
    | t :: rest => (LTask t :: ilog I (head_state (xs s) t rest) (run_task R (rs s) t), [t])
    | [] => ([], [])
    end
    end
    end
  end.

(** What one step does, seen from the runtime: either nothing, or one task. *)
Lemma step_log_cases : forall R I Sch s,
  (step_log R I Sch s = ([], []) /\ rs (step R I Sch s) = rs s) \/
  (exists t rest, phase (xs s) <> PDone /\ queue (xs s) = t :: rest /\
     step_log R I Sch s =
       (LTask t :: ilog I (head_state (xs s) t rest) (run_task R (rs s) t), [t]) /\
     rs (step R I Sch s) = snd (interp I (head_state (xs s) t rest) (run_task R (rs s) t)) /\
     xs (step R I Sch s) = set_micro (fst (interp I (head_state (xs s) t rest)
                                             (run_task R (rs s) t))) (S (micro (xs s)))).
Proof.
  intros R I Sch s; unfold step_log, step; cbv beta zeta.
  destruct (phase (xs s)) eqn:P; [| | left; auto];
    (destruct (stop_due Sch (xs s)); [left; auto |]);
    (destruct (foreign_due I (xs s)); [left; auto |]);
    (destruct (cut_due Sch (xs s)); [left; auto |]);
    (destruct (queue (xs s)) as [| t rest];
       [destruct (at_boundary I Sch (xs s)); left; auto |]);
    right; exists t, rest; rewrite step_run_head_eq;
    destruct (interp I (head_state (xs s) t rest) (run_task R (rs s) t)); cbn;
    repeat split; auto; congruence.
Qed.

Fixpoint elog (R : Runtime) (I : Inputs) (Sch : Schedule) (n : nat) (s : Sys R)
    : list LogEntry * list Task :=
  match n with
  | O => ([], [])
  | S m =>
      let '(l1, t1) := step_log R I Sch s in
      let '(l2, t2) := elog R I Sch m (step R I Sch s) in
      (l1 ++ l2, t1 ++ t2)
  end.

Theorem step_drive_elog : forall R I Sch n s A c d,
  answers_ok A c d (fst (elog R I Sch n s)) ->
  drive R A c d (rs s) (snd (elog R I Sch n s)) =
    (fst (elog R I Sch n s), rs (iterate R I Sch n s)).
Proof.
  intros R I Sch n; induction n as [| n IH]; intros s A c d H; [reflexivity |].
  cbn [elog iterate] in *.
  destruct (step_log_cases R I Sch s) as [[E Hr] | (t & rest & P & Q & E & Hr & Hx)].
  - rewrite E in *; destruct (elog R I Sch n (step R I Sch s)) as [l2 t2] eqn:E2.
    cbn in *; rewrite <- Hr; specialize (IH (step R I Sch s) A c d); rewrite E2 in IH.
    apply IH; auto.
  - rewrite E in *; destruct (elog R I Sch n (step R I Sch s)) as [l2 t2] eqn:E2.
    cbn in H |- *.
    set (L1 := ilog I (head_state (xs s) t rest) (run_task R (rs s) t)) in *.
    apply step_answers_ok_app in H; destruct H as [H1 H2].
    rewrite (step_play_ilog I _ _ A c d H1); fold L1.
    specialize (IH (step R I Sch s) A (c + length (clocks L1))%nat
                   (d + length (draw_values L1))%nat).
    rewrite E2 in IH; cbn in IH; rewrite <- Hr, IH; auto.
Qed.

(** ** The answer table read from a log *)

Definition answers_of (L : list LogEntry) : Answers :=
  {| clock_answer := fun i => nth i (clocks L) 0;
     draw_answer := fun i => nth i (draw_values L) 0%nat;
     register_answer := fun _ => false |}.

Lemma step_answers_of_ok : forall L2 L1,
  (forall f b, In (LRegister f b) L2 -> b = false) ->
  answers_ok (answers_of (L1 ++ L2)) (length (clocks L1)) (length (draw_values L1)) L2.
Proof.
  intros L2; induction L2 as [| e L2 IH]; intros L1 Hr; cbn; auto.
  assert (Hr' : forall f b, In (LRegister f b) L2 -> b = false) by (intros; eauto using in_cons).
  destruct e as [t | ev | f l | f r | f b].
  - specialize (IH (L1 ++ [LTask t]) Hr'); rewrite <- app_assoc in IH; cbn in IH.
    unfold clocks, draw_values in *; rewrite !flat_map_app, !length_app in IH; cbn in IH.
    rewrite !Nat.add_0_r in IH; exact IH.
  - specialize (IH (L1 ++ [LEvent ev]) Hr'); rewrite <- app_assoc in IH; cbn in IH.
    unfold clocks, draw_values in *; rewrite !flat_map_app, !length_app in IH; cbn in IH.
    rewrite !Nat.add_0_r in IH; exact IH.
  - split.
    + unfold clocks; rewrite flat_map_app; cbn; apply nth_middle.
    + specialize (IH (L1 ++ [LClock f l]) Hr'); rewrite <- app_assoc in IH; cbn in IH.
      unfold clocks, draw_values in *; rewrite !flat_map_app, !length_app in IH; cbn in IH.
      rewrite Nat.add_0_r, Nat.add_1_r in IH; exact IH.
  - split.
    + unfold draw_values; rewrite flat_map_app; cbn; apply nth_middle.
    + specialize (IH (L1 ++ [LDraw f r]) Hr'); rewrite <- app_assoc in IH; cbn in IH.
      unfold clocks, draw_values in *; rewrite !flat_map_app, !length_app in IH; cbn in IH.
      rewrite Nat.add_0_r, Nat.add_1_r in IH; exact IH.
  - split; [symmetry; apply (Hr f b); left; reflexivity |].
    specialize (IH (L1 ++ [LRegister f b]) Hr'); rewrite <- app_assoc in IH; cbn in IH.
    unfold clocks, draw_values in *; rewrite !flat_map_app, !length_app in IH; cbn in IH.
    rewrite !Nat.add_0_r in IH; exact IH.
Qed.

(** ** Registrations answered [true] happen only during closing *)

Lemma step_closed_step : forall R I Sch s, phase (xs s) <> POpen ->
  phase (xs (step R I Sch s)) <> POpen.
Proof.
  intros R I Sch s P; rewrite step_xs.
  destruct (phase (xs s)) eqn:E; [congruence | | rewrite E; congruence].
  destruct (stop_due Sch (xs s)); [fields; discriminate |].
  destruct (foreign_due I (xs s)) as [fi |].
  { fields; destruct fi; cbn [on_foreign]; try (apply step_violate_phase; fields; congruence);
      fields; congruence. }
  destruct (cut_due Sch (xs s)) as [k |].
  { fields; unfold on_cut; destruct k;
      try (apply step_close_phase; fields; congruence); fields; discriminate. }
  destruct (queue (xs s)) as [| t rest].
  - unfold at_boundary; rewrite E; fields; discriminate.
  - fields; rewrite step_run_head_eq.
    destruct (step_head_state_closed (xs s) t rest) as [P1 _].
    apply (step_interp_closed I (run_task R (rs s) t)); congruence.
Qed.

Lemma step_closed_iterate : forall R I Sch n s, phase (xs s) <> POpen ->
  phase (xs (iterate R I Sch n s)) <> POpen.
Proof.
  intros R I Sch n; induction n as [| n IH]; intros s P; cbn; auto.
  apply IH, step_closed_step; auto.
Qed.

Lemma step_ilog_register : forall {X} I (s : Script X) x f,
  In (LRegister f true) (ilog I x s) -> phase (fst (interp I x s)) <> POpen.
Proof.
  intros X I s; induction s as [r | e k IH | g k IH | g k IH | g k IH]; intros x f H;
    cbn in *; try (destruct H as [H | H]; [discriminate | eauto]).
  - contradiction.
  - destruct H as [H | H]; [| eauto].
    inversion H; subst.
    apply step_interp_closed; fields.
    destruct (phase x); congruence.
Qed.

Lemma step_elog_register : forall R I Sch n s f,
  In (LRegister f true) (fst (elog R I Sch n s)) -> phase (xs (iterate R I Sch n s)) <> POpen.
Proof.
  intros R I Sch n; induction n as [| n IH]; intros s f H; cbn in *; [contradiction |].
  destruct (step_log_cases R I Sch s) as [[E Hr] | (t & rest & P & Q & E & Hr & Hx)];
    rewrite E in H; destruct (elog R I Sch n (step R I Sch s)) as [l2 t2] eqn:E2;
    cbn in H; specialize (IH (step R I Sch s) f); rewrite E2 in IH; cbn in IH; auto.
  destruct H as [H | H]; [discriminate |].
  apply in_app_or in H; destruct H as [H | H]; auto.
  apply step_closed_iterate; rewrite Hx; fields.
  eapply step_ilog_register; eauto.
Qed.

(** The log of a run that is still open is what the runtime reports when driven with the
    run's tasks and the answers read from the log. *)
Theorem step_open_log_is_drive : forall R I Sch n s,
  phase (xs (iterate R I Sch n s)) = POpen ->
  let L := elog R I Sch n s in
  fst (drive R (answers_of (fst L)) 0 0 (rs s) (snd L)) = fst L.
Proof.
  intros R I Sch n s P L.
  assert (H : answers_ok (answers_of (fst L)) 0 0 (fst L)).
  { apply (step_answers_of_ok (fst L) []).
    intros f b Hin; destruct b; auto.
    exfalso; apply (step_elog_register R I Sch n s f Hin); auto. }
  unfold L; rewrite step_drive_elog; auto.
Qed.
