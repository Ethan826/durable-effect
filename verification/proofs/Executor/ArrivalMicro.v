(** * Arrival: the executor's functions never read the micro-step counter.

    Every function below the step commutes with [set_micro]: changing the counter before it
    runs changes only the counter after it. Only [at_boundary_sub] reads the counter, through
    the arrival schedule, so under [arrival_sinf] the step commutes too, up to the counter
    itself. *)

From Coq Require Import List ZArith Bool Arith.
From Durable Require Import Runtime Exec Statements ArrivalBase.
Import ListNotations.
Open Scope Z_scope.

Ltac arrival_mic_by fs :=
  intros; match goal with x : XState |- _ => destruct x end; unfold fs; arrival_norm;
  arrival_split.

Lemma arrival_issue_micro : forall I x m k o s,
  issue I (set_micro x m) k o s = set_micro (issue I x k o s) m.
Proof. intros. destruct x. unfold issue, finish. arrival_norm. arrival_split. Qed.

Lemma arrival_violate_micro : forall x m v,
  violate (set_micro x m) v = set_micro (violate x v) m.
Proof. intros. destruct x. unfold violate, close. arrival_norm. arrival_split. Qed.

Lemma arrival_on_start_micro : forall I x m f tok op,
  on_start I (set_micro x m) f tok op = set_micro (on_start I x f tok op) m.
Proof.
  intros. destruct x.
  unfold on_start, slot_held, violate, close, issue_op, issue, finish.
  arrival_norm. arrival_split.
Qed.

Lemma arrival_on_event_micro : forall I x m e,
  on_event I (set_micro x m) e = set_micro (on_event I x e) m.
Proof.
  intros. destruct x.
  unfold on_event, on_start, slot_held, violate, close, issue_op, issue, finish, on_release.
  arrival_norm. arrival_split.
Qed.

Lemma arrival_interp_micro : forall {X} I (s : Script X) x m,
  interp I (set_micro x m) s = (set_micro (fst (interp I x s)) m, snd (interp I x s)).
Proof.
  intros X I s. induction s as [r|e k IH|f k IH|f k IH|f k IH]; intros x m; cbn [interp].
  - reflexivity.
  - rewrite arrival_on_event_micro. apply IH.
  - change (logical (set_micro x m)) with (logical x).
    change (phase (set_micro x m)) with (phase x).
    destruct (phase x); try apply (IH (logical x));
      rewrite arrival_emit_micro; apply (IH (logical x)).
  - change (draws (set_micro x m)) with (draws x).
    change (phase (set_micro x m)) with (phase x).
    destruct (phase x); try apply (IH (stream I (draws x)));
      change (set_draws (set_micro x m) (S (draws x)))
        with (set_micro (set_draws x (S (draws x))) m);
      rewrite arrival_emit_micro; apply (IH (stream I (draws x))).
  - change (phase (set_micro x m)) with (phase x).
    destruct (phase x);
      [change (set_live (emit (set_micro x m) (ARegister f))
                 (live (emit (set_micro x m) (ARegister f)) ++ [f]))
         with (set_micro (set_live (emit x (ARegister f))
                 (live (emit x (ARegister f)) ++ [f])) m)
      |change (set_live (emit (set_micro x m) (ARegister f))
                 (live (emit (set_micro x m) (ARegister f)) ++ [f]))
         with (set_micro (set_live (emit x (ARegister f))
                 (live (emit x (ARegister f)) ++ [f])) m)
      |change (set_live (set_micro x m) (live (set_micro x m) ++ [f]))
         with (set_micro (set_live x (live x ++ [f])) m)];
      apply IH.
Qed.

Lemma arrival_run_head_micro : forall R I x m r t rest,
  run_head R I (set_micro x m) r t rest =
  (set_micro (fst (run_head R I x r t rest)) m, snd (run_head R I x r t rest)).
Proof.
  intros. unfold run_head.
  match goal with |- interp I ?a ?s = _ =>
    match goal with |- _ = (_ (fst (interp I ?b _)) _, _) =>
      replace a with (set_micro b m) end end.
  - apply arrival_interp_micro.
  - destruct x. arrival_norm. arrival_split.
Qed.

Lemma arrival_on_foreign_micro : forall x m fi,
  on_foreign (set_micro x m) fi = set_micro (on_foreign x fi) m.
Proof.
  intros. destruct x. unfold on_foreign, violate, close. arrival_norm. arrival_split.
Qed.

Lemma arrival_on_cut_micro : forall x m k,
  on_cut (set_micro x m) k = set_micro (on_cut x k) m.
Proof. intros. destruct x. unfold on_cut, close. arrival_norm. arrival_split. Qed.

Lemma arrival_apply_sample_micro : forall x m c v a,
  apply_sample (set_micro x m) c v a = set_micro (apply_sample x c v a) m.
Proof.
  intros. destruct x. unfold apply_sample, violate, close. arrival_norm. arrival_split.
Qed.

Lemma arrival_issue_sample_micro : forall I x m a,
  issue_sample I (set_micro x m) a = set_micro (issue_sample I x a) m.
Proof. intros. apply arrival_issue_micro. Qed.

Lemma arrival_issue_op_micro : forall I x m f tok op,
  issue_op I (set_micro x m) f tok op = set_micro (issue_op I x f tok op) m.
Proof.
  intros. unfold issue_op. destruct op as [|d]; [apply arrival_issue_micro|].
  destruct d; cbv zeta; [destruct (split d)|]; apply arrival_issue_micro.
Qed.

Lemma arrival_after_sample_micro : forall I x m a,
  after_sample I (set_micro x m) a = set_micro (after_sample I x a) m.
Proof.
  intros. unfold after_sample. destruct a; try reflexivity; try apply arrival_issue_micro.
  destruct (link_of rest) as [[]|]; [apply arrival_issue_micro|reflexivity].
Qed.

Lemma arrival_on_notify_micro : forall I x m sb r,
  on_notify I (set_micro x m) sb r = set_micro (on_notify I x sb r) m.
Proof.
  intros. unfold on_notify.
  destruct sb as [c f tok op k rest|c a|c]; destruct r; try destruct op;
    try destruct a; try reflexivity;
    try apply arrival_issue_micro; try apply arrival_violate_micro;
    rewrite arrival_apply_sample_micro;
    match goal with |- context [phase (set_micro ?y m)] =>
      change (phase (set_micro y m)) with (phase y); destruct (phase y) end;
    try reflexivity; apply arrival_after_sample_micro.
Qed.

Lemma arrival_on_cancel_micro : forall I x m sb,
  on_cancel I (set_micro x m) sb = set_micro (on_cancel I x sb) m.
Proof.
  intros. unfold on_cancel.
  destruct sb as [c f tok op k rest|c a|c]; try destruct a; try reflexivity;
    try apply arrival_issue_micro.
  change (set_held (set_micro x m) true) with (set_micro (set_held x true) m).
  apply arrival_issue_micro.
Qed.

Lemma arrival_at_boundary_sub_micro : forall I x m sb,
  at_boundary_sub I (arrival_sinf I) (set_micro x m) sb =
  option_map (fun y => set_micro y m) (at_boundary_sub I (arrival_sinf I) x sb).
Proof.
  intros. unfold at_boundary_sub. cbn [arrival_sinf arrived].
  change (cursor (set_micro x m)) with (cursor x).
  change (next_cmd (set_micro x m)) with (next_cmd x).
  destruct (length (entries I) <=? cursor x)%nat; [reflexivity|].
  destruct (nth_error (entries I) (cursor x)) as [[c r|]|]; cbn [option_map];
    try reflexivity.
  - destruct (Nat.eqb c (sub_cmd sb)); [|destruct (c <? next_cmd x)%nat; reflexivity].
    change (set_cursor (set_micro x m) (S (cursor x)))
      with (set_micro (set_cursor x (S (cursor x))) m).
    rewrite arrival_on_notify_micro. reflexivity.
  - change (set_cursor (set_micro x m) (S (cursor x)))
      with (set_micro (set_cursor x (S (cursor x))) m).
    rewrite arrival_on_cancel_micro. reflexivity.
Qed.

Lemma arrival_at_boundary_micro : forall I x m,
  at_boundary I (arrival_sinf I) (set_micro x m) =
  option_map (fun y => set_micro y m) (at_boundary I (arrival_sinf I) x).
Proof.
  intros. unfold at_boundary.
  change (phase (set_micro x m)) with (phase x).
  change (held (set_micro x m)) with (held x).
  change (waiter (set_micro x m)) with (waiter x).
  change (sub (set_micro x m)) with (sub x).
  destruct (phase x); [|destruct x; reflexivity|reflexivity].
  destruct (held x), (waiter x) as [[[f tok] op]|]; try (destruct x; reflexivity);
    destruct (sub x) as [sb|]; try apply arrival_at_boundary_sub_micro;
    cbn [option_map]; f_equal;
    try (rewrite <- arrival_issue_op_micro; reflexivity);
    apply arrival_violate_micro.
Qed.

Lemma arrival_step_micro : forall R I x m r,
  let s1 := step R I (arrival_sinf I) {| xs := set_micro x m; rs := r |} in
  let s2 := step R I (arrival_sinf I) {| xs := x; rs := r |} in
  arrival_strip (xs s1) = arrival_strip (xs s2) /\ rs s1 = rs s2.
Proof.
  intros. subst s1 s2. unfold step. cbn [xs rs].
  change (phase (set_micro x m)) with (phase x).
  change (micro (set_micro x m)) with m.
  change (foreign_due I (set_micro x m)) with (foreign_due I x).
  change (queue (set_micro x m)) with (queue x).
  destruct (phase x) eqn:Hp; [| |split; reflexivity];
    cbn [stop_due cut_due arrival_sinf stop_at cut_at];
    (destruct (foreign_due I x) as [fi|];
     [change (progress (set_micro x m)) with (progress x);
      change (set_fseen (set_micro x m) (Some (progress x)))
        with (set_micro (set_fseen x (Some (progress x))) m);
      rewrite arrival_on_foreign_micro; split; reflexivity|]);
    (destruct (queue x) as [|t rest];
     [rewrite arrival_at_boundary_micro;
      destruct (at_boundary I (arrival_sinf I) x); cbn [option_map];
      split; reflexivity
     |rewrite arrival_run_head_micro; destruct (run_head R I x r t rest);
      split; reflexivity]).
Qed.
