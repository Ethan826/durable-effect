(** * The executor drives the runtime as [drive] does, so I4 and I7 apply to it.

    The tasks an attempt runs, and the log of what each task reported and was answered, are
    defined alongside the executor's steps. With the answers the executor gave, [drive]
    reproduces that log: the clock and draw answers are read off the log by position, and
    each fiber's registration answer is the one it got the first time it registered, which
    is the only time by I7. I4 then says the log starts no token twice, and the executor's
    trace starts a subsequence of the log's tokens. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Rev3 Statements TimeBase TimeStep TimeFresh1.
Import ListNotations.
Open Scope Z_scope.

(** ** The log of a task *)

(** What a script reports and is answered, as [interp] answers it. *)
Fixpoint time_ilog {X} (I : Inputs) (x : XState) (s : Script X) : list LogEntry :=
  match s with
  | Done _ => []
  | Emit e k => LEvent e :: time_ilog I (on_event I x e) k
  | AskClock f k =>
      LClock f (logical x) ::
        time_ilog I (match phase x with PDone => x | _ => emit x (AClock f (logical x)) end)
          (k (logical x))
  | AskDraw f k =>
      LDraw f (stream I (draws x)) ::
        time_ilog I (match phase x with
                     | PDone => x
                     | _ => emit (set_draws x (S (draws x))) (ADraw f (stream I (draws x)))
                     end) (k (stream I (draws x)))
  | Register f k =>
      let closing := match phase x with PClosing _ => true | _ => false end in
      LRegister f closing :: time_ilog I (set_live x (live x ++ [f])) (k closing)
  end.

Lemma time_interp_sub : forall I X (s : Script X) x,
  time_grows_sub x (fst (interp I x s)) (start_tokens (time_ilog I x s)).
Proof.
  intros I X s. induction s as [r|e k IH|f k IH|f k IH|f k IH]; intros x;
    cbn [interp time_ilog].
  - apply time_grows_sub_nostart. apply time_nostart_refl.
  - replace (start_tokens (LEvent e :: time_ilog I (on_event I x e) k)) with
      (start_tokens [LEvent e] ++ start_tokens (time_ilog I (on_event I x e) k))
      by (unfold start_tokens; rewrite <- flat_map_app; reflexivity).
    eapply time_grows_sub_trans; [apply time_grows_sub_event|apply IH].
  - replace (start_tokens (LClock f (logical x) :: _)) with ([] ++ start_tokens
      (time_ilog I (match phase x with PDone => x | _ => emit x (AClock f (logical x)) end)
         (k (logical x)))) by reflexivity.
    eapply time_grows_sub_trans; [|apply IH]. apply time_grows_sub_nostart.
    destruct (phase x); try (apply time_nostart_emit; discriminate); apply time_nostart_refl.
  - replace (start_tokens (LDraw f (stream I (draws x)) :: _)) with ([] ++ start_tokens
      (time_ilog I (match phase x with
                     | PDone => x
                     | _ => emit (set_draws x (S (draws x))) (ADraw f (stream I (draws x)))
                     end) (k (stream I (draws x))))) by reflexivity.
    eapply time_grows_sub_trans; [|apply IH]. apply time_grows_sub_nostart.
    destruct (phase x); try (eapply time_nostart_trans;
      [apply (time_nostart_same _ (set_draws x (S (draws x)))); reflexivity
      |apply time_nostart_emit; discriminate]); apply time_nostart_refl.
  - replace (start_tokens (LRegister f _ :: _)) with ([] ++ start_tokens
      (time_ilog I (set_live x (live x ++ [f]))
         (k match phase x with PClosing _ => true | _ => false end))) by reflexivity.
    eapply time_grows_sub_trans; [|apply IH]. apply time_grows_sub_nostart.
    apply time_nostart_same. reflexivity.
Qed.

(** ** The tasks of a step *)

(** The state a task's script starts from, as [run_head] builds it. *)
Definition time_x2 (x : XState) (t : Task) (rest : list Task) : XState :=
  let x0 := set_progress (set_queue x rest) (S (progress x)) in
  let x1 := match task_action t with Some a => emit x0 a | None => x0 end in
  match t, awaiter x1 with
  | Deliver f tok _, Some a | DeliverCancel f tok, Some a =>
      if pair_eqb a (f, tok) then set_awaiter x1 None else x1
  | _, _ => x1
  end.

Lemma time_run_head_x2 : forall R I x r t rest,
  run_head R I x r t rest = interp I (time_x2 x t rest) (run_task R r t).
Proof. reflexivity. Qed.

(** The task a step runs, and the rest of the queue, if it runs one. *)
Definition time_step_task (R : Runtime) (I : Inputs) (Sch : Schedule) (s : Sys R)
    : option (Task * list Task) :=
  let x := xs s in
  match phase x with
  | PDone => None
  | _ =>
    if stop_due Sch x then None else
    match foreign_due I x with
    | Some _ => None
    | None =>
    match cut_due Sch x with
    | Some _ => None
    | None => match queue x with t :: rest => Some (t, rest) | [] => None end
    end
    end
  end.

Lemma time_nostart_x2 : forall x t rest, time_nostart x (time_x2 x t rest).
Proof.
  intros x t rest. unfold time_x2.
  assert (H1 : time_nostart x (match task_action t with
     | Some a => emit (set_progress (set_queue x rest) (S (progress x))) a
     | None => set_progress (set_queue x rest) (S (progress x)) end)).
  { destruct t; cbn [task_action]; try (apply time_nostart_same; reflexivity);
      (eapply time_nostart_trans;
       [apply (time_nostart_same _ (set_progress (set_queue x rest) (S (progress x))));
        reflexivity|apply time_nostart_emit; discriminate]). }
  destruct t; try exact H1;
    destruct (awaiter _) as [a|]; try exact H1; destruct (pair_eqb a _); try exact H1;
    (eapply time_nostart_trans; [exact H1|apply time_nostart_same; reflexivity]).
Qed.

Lemma time_step_cases : forall R I Sch s,
  match time_step_task R I Sch s with
  | None => time_nostart (xs s) (xs (step R I Sch s)) /\ rs (step R I Sch s) = rs s
  | Some (t, rest) =>
      time_nostart (xs s) (time_x2 (xs s) t rest) /\
      trace (xs (step R I Sch s)) = trace (fst (interp I (time_x2 (xs s) t rest)
                                                  (run_task R (rs s) t))) /\
      rs (step R I Sch s) = snd (interp I (time_x2 (xs s) t rest) (run_task R (rs s) t))
  end.
Proof.
  intros R I Sch s. unfold time_step_task, step. cbv zeta.
  destruct (phase (xs s)); [| |split; [apply time_nostart_refl|reflexivity]].
  all: destruct (stop_due Sch (xs s));
    [split; [apply time_nostart_same; reflexivity|reflexivity]|].
  all: destruct (foreign_due I (xs s)) as [fi|];
    [split; [|reflexivity]; eapply time_nostart_trans;
     [apply (time_nostart_same _ (set_fseen (xs s) (Some (progress (xs s))))); reflexivity|];
     eapply time_nostart_trans; [apply time_nostart_foreign|];
     apply time_nostart_same; reflexivity|].
  all: destruct (cut_due Sch (xs s)) as [k|];
    [split; [|reflexivity]; eapply time_nostart_trans; [apply time_nostart_cut|];
     apply time_nostart_same; reflexivity|].
  all: destruct (queue (xs s)) as [|t rest];
    [destruct (at_boundary I Sch (xs s)) as [x'|] eqn:B;
     (split; [|reflexivity]);
     [eapply time_nostart_trans; [eapply time_nostart_boundary; exact B|];
      apply time_nostart_same; reflexivity
     |apply time_nostart_same; reflexivity]
    |].
  all: rewrite time_run_head_x2;
    destruct (interp I (time_x2 (xs s) t rest) (run_task R (rs s) t)) as [x' r'] eqn:E;
    split; [apply time_nostart_x2|]; split; reflexivity.
Qed.

(** The log of a step, and the tasks and log of [n] steps. *)
Definition time_step_log (R : Runtime) (I : Inputs) (Sch : Schedule) (s : Sys R)
    : list LogEntry :=
  match time_step_task R I Sch s with
  | Some (t, rest) => LTask t :: time_ilog I (time_x2 (xs s) t rest) (run_task R (rs s) t)
  | None => []
  end.

Fixpoint time_tasks (R : Runtime) (I : Inputs) (Sch : Schedule) (n : nat) (s : Sys R)
    : list Task :=
  match n with
  | O => []
  | S m => match time_step_task R I Sch s with Some (t, _) => [t] | None => [] end ++
           time_tasks R I Sch m (step R I Sch s)
  end.

Fixpoint time_log (R : Runtime) (I : Inputs) (Sch : Schedule) (n : nat) (s : Sys R)
    : list LogEntry :=
  match n with
  | O => []
  | S m => time_step_log R I Sch s ++ time_log R I Sch m (step R I Sch s)
  end.

Lemma time_start_tokens_app : forall a b,
  start_tokens (a ++ b) = start_tokens a ++ start_tokens b.
Proof. intros. unfold start_tokens. apply flat_map_app. Qed.

Lemma time_run_sub : forall R I Sch n s,
  time_grows_sub (xs s) (xs (iterate R I Sch n s)) (start_tokens (time_log R I Sch n s)).
Proof.
  intros R I Sch n. induction n as [|n IH]; intros s; cbn [iterate time_log].
  - apply time_grows_sub_nostart. apply time_nostart_refl.
  - rewrite time_start_tokens_app. eapply time_grows_sub_trans; [|apply IH].
    pose proof (time_step_cases R I Sch s) as C. unfold time_step_log.
    destruct (time_step_task R I Sch s) as [[t rest]|].
    + destruct C as [N [T _]]. cbn [start_tokens flat_map app].
      replace (flat_map _ _) with ([] ++ start_tokens
        (time_ilog I (time_x2 (xs s) t rest) (run_task R (rs s) t))) by reflexivity.
      eapply time_grows_sub_trans; [apply time_grows_sub_nostart; exact N|].
      destruct (time_interp_sub I _ (run_task R (rs s) t) (time_x2 (xs s) t rest))
        as [r [Tr Sr]].
      exists r. rewrite T, Tr. auto.
    + apply time_grows_sub_nostart. exact (proj1 C).
Qed.
