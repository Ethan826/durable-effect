(** * Step domain: the trace only grows.

    Every step appends to the trace and never rewrites it. [grows x y] says [y]'s trace is
    [x]'s with something appended. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Statements StepInv StepTurn.
Import ListNotations.
Open Scope Z_scope.

Definition grows (x y : XState) : Prop := exists suf, trace y = trace x ++ suf.

Lemma step_grows_refl : forall x, grows x x.
Proof. intros x; exists []; rewrite app_nil_r; reflexivity. Qed.

Lemma step_grows_trans : forall x y z, grows x y -> grows y z -> grows x z.
Proof.
  intros x y z [s1 H1] [s2 H2]; exists (s1 ++ s2); rewrite H2, H1, app_assoc; reflexivity.
Qed.

Lemma step_grows_same : forall x y, trace y = trace x -> grows x y.
Proof. intros x y H; exists []; rewrite H, app_nil_r; reflexivity. Qed.

Lemma step_grows_emit : forall x a, grows x (emit x a).
Proof. intros x a; exists [a]; reflexivity. Qed.

Lemma step_grows_nce : forall x y, no_cmd_ext x y -> grows x y.
Proof. intros x y [_ [suf [T _]]]; exists suf; exact T. Qed.

Lemma step_grows_close : forall x c, grows x (close x c).
Proof. intros; apply step_grows_same, step_close_trace. Qed.

Lemma step_grows_violate : forall x v, grows x (violate x v).
Proof. intros; apply step_grows_nce, step_nce_violate. Qed.

Lemma step_grows_issue : forall I x k o s, grows x (issue I x k o s).
Proof.
  intros; destruct (step_issue_trace I x k o s) as [E | E]; eexists; exact E.
Qed.

Lemma step_grows_issue_op : forall I x f tok op, grows x (issue_op I x f tok op).
Proof.
  intros; unfold issue_op; destruct op as [kk a | d];
    [| destruct (match d with Millis m => split m | Forever => (max_chunk, Endless) end)];
    apply step_grows_issue.
Qed.

Lemma step_grows_apply_sample : forall x c v a, grows x (apply_sample x c v a).
Proof.
  intros; destruct (step_apply_sample_cases x c v a) as [E | (a' & l & _ & E)]; rewrite E;
    [apply step_grows_violate | exists [a']; reflexivity].
Qed.

Lemma step_grows_after_sample : forall I y a, grows y (after_sample I y a).
Proof.
  intros I y a; destruct a; cbn [after_sample];
    try (apply step_grows_same; reflexivity).
  destruct (link_of _) as [[? ?] |]; [apply step_grows_issue | apply step_grows_same; auto].
Qed.

Lemma step_grows_on_notify : forall I x s r, grows x (on_notify I x s r).
Proof.
  intros I x s r; unfold on_notify.
  destruct s as [c f tok op k rest | c after | c];
    [destruct op, r | destruct r, after | ]; cbv zeta;
    try apply step_grows_issue; try apply step_grows_violate;
    try (apply step_grows_same; reflexivity);
    match goal with |- context [apply_sample ?x ?c ?v ?a] =>
      destruct (phase (apply_sample x c v a));
      try (eapply step_grows_trans; [apply step_grows_apply_sample |
                                     apply step_grows_after_sample]);
      apply step_grows_apply_sample end.
Qed.

Lemma step_grows_on_cancel : forall I x s, grows x (on_cancel I x s).
Proof.
  intros I x s; destruct s as [c f tok op k rest | c after | c];
    [| destruct after |]; cbn [on_cancel]; try (apply step_grows_same; reflexivity);
    try apply step_grows_issue.
  eapply step_grows_trans; [apply (step_grows_same x (set_held x true)); reflexivity |].
  apply step_grows_issue.
Qed.

Lemma step_grows_on_start : forall I x f tok op, grows x (on_start I x f tok op).
Proof.
  intros I x f tok op; unfold on_start; destruct (phase x).
  - cbv zeta; eapply step_grows_trans; [apply (step_grows_emit x (AStart f tok op)) |].
    destruct (zero_sleep op); [apply step_grows_same; reflexivity |].
    destruct (awaiter _); [apply step_grows_violate |].
    destruct (held _); [apply step_grows_same; reflexivity |].
    destruct (slot_held _); [apply step_grows_same; reflexivity |].
    eapply step_grows_trans; [| apply step_grows_issue_op].
    apply step_grows_same; reflexivity.
  - eapply step_grows_trans; [apply (step_grows_emit x (AStart f tok op)) |].
    apply step_grows_same; reflexivity.
  - apply step_grows_refl.
Qed.

Lemma step_grows_on_release : forall x f tok, grows x (on_release x f tok).
Proof.
  intros x f tok; rewrite step_on_release_split.
  destruct (step_release_pre_fields x f tok) as (_ & _ & _ & _ & T & _).
  apply step_grows_same; rewrite <- T.
  generalize (release_pre x f tok); intros y; unfold release_rest.
  destruct (phase y); auto; destruct (awaiter y); auto; destruct (negb _); auto.
  cbv zeta; destruct (waiter y); auto; destruct (sub y); auto.
  destruct (release_sub _) as [[[? ?] ?] |]; auto; destruct (pair_eqb _ _); auto.
Qed.

Lemma step_grows_on_event : forall I x e, grows x (on_event I x e).
Proof.
  intros I x e; unfold on_event.
  assert (H : grows x (match e with
                       | EvStart f tok op => on_start I x f tok op
                       | EvRelease f tok => on_release x f tok
                       | EvQueue p t => if Nat.eqb p 0 then enqueue x (RunQueued t)
                                        else violate x Priority
                       | EvFiberExited f => set_live x (remove_fiber f (live x))
                       | EvRootExit r =>
                           match root_exit x with
                           | Some _ => violate x SecondExit
                           | None => close (set_root_exit x (Some r)) None
                           end
                       end)).
  { destruct e as [f tok op | f tok | pr t | f | r].
    - apply step_grows_on_start.
    - apply step_grows_on_release.
    - destruct (Nat.eqb pr 0); [apply step_grows_same; reflexivity | apply step_grows_violate].
    - apply step_grows_same; reflexivity.
    - destruct (root_exit x); [apply step_grows_violate |].
      eapply step_grows_trans; [| apply step_grows_close]; apply step_grows_same; reflexivity. }
  destruct (phase x); auto; apply step_grows_refl.
Qed.

Lemma step_grows_interp : forall {X} I (s : Script X) x, grows x (fst (interp I x s)).
Proof.
  intros X I s; induction s as [r | e k IH | f k IH | f k IH | f k IH]; intros x; cbn.
  - apply step_grows_refl.
  - eapply step_grows_trans; [apply step_grows_on_event | apply IH].
  - eapply step_grows_trans; [| apply IH].
    destruct (phase x); try apply step_grows_emit; apply step_grows_refl.
  - eapply step_grows_trans; [| apply IH].
    destruct (phase x); try apply step_grows_refl;
      (eapply step_grows_trans; [| apply step_grows_emit]); apply step_grows_same; reflexivity.
  - eapply step_grows_trans; [| apply IH].
    set (y := match phase x with PDone => x | _ => emit x (ARegister f) end).
    apply (step_grows_trans _ y).
    + unfold y; destruct (phase x); try apply step_grows_emit; apply step_grows_refl.
    + apply step_grows_same; reflexivity.
Qed.

Lemma step_grows_head : forall x t rest, grows x (head_state x t rest).
Proof. intros; apply step_grows_nce, step_head_state_closed. Qed.

Lemma step_grows_boundary_sub : forall I Sch x s y, at_boundary_sub I Sch x s = Some y ->
  grows x y.
Proof.
  intros I Sch x s y E; unfold at_boundary_sub in E.
  destruct (arrived Sch (micro x) <=? cursor x)%nat; [discriminate |].
  destruct (nth_error (entries I) (cursor x)) as [[c r |] |]; [| | discriminate].
  - destruct (Nat.eqb c (sub_cmd s)).
    + inversion E; subst; eapply step_grows_trans; [| apply step_grows_on_notify].
      apply step_grows_same; reflexivity.
    + destruct (c <? next_cmd x)%nat; inversion E; subst; apply step_grows_same; auto.
  - inversion E; subst; eapply step_grows_trans; [| apply step_grows_on_cancel].
    apply step_grows_same; reflexivity.
Qed.

Lemma step_grows_boundary : forall I Sch x y, at_boundary I Sch x = Some y -> grows x y.
Proof.
  intros I Sch x y E; unfold at_boundary in E.
  destruct (phase x); [| inversion E; subst; unfold finish;
                         eapply step_grows_trans; [apply step_grows_emit |];
                         apply step_grows_same; reflexivity | discriminate].
  destruct (held x), (waiter x) as [[[f tok] op] |];
    try (inversion E; subst; apply step_grows_same; reflexivity);
    (destruct (sub x) as [s |]; [eapply step_grows_boundary_sub; eauto |]);
    inversion E; subst; try apply step_grows_violate.
  eapply step_grows_trans; [| apply step_grows_issue_op]; apply step_grows_same; reflexivity.
Qed.

Lemma step_grows_step : forall R I Sch s, grows (xs s) (xs (step R I Sch s)).
Proof.
  intros R I Sch s; rewrite step_xs.
  assert (Hm : forall y v, grows (xs s) y -> grows (xs s) (set_micro y v))
    by (intros y v [suf H]; exists suf; exact H).
  destruct (phase (xs s)); try apply step_grows_refl;
    (destruct (stop_due Sch (xs s)); [apply Hm, step_grows_same; reflexivity |]);
    (destruct (foreign_due I (xs s)) as [fi |];
       [apply Hm; eapply step_grows_trans;
          [apply (step_grows_same _ (set_fseen (xs s) (Some (progress (xs s))))); reflexivity |];
        destruct fi; cbn [on_foreign]; try apply step_grows_violate; apply step_grows_refl |]);
    (destruct (cut_due Sch (xs s)) as [k |];
       [apply Hm; unfold on_cut; eapply step_grows_trans; [apply step_grows_emit |];
        destruct k; try apply step_grows_close; apply step_grows_same; reflexivity |]);
    (destruct (queue (xs s)) as [| t rest];
       [destruct (at_boundary I Sch (xs s)) eqn:E;
          [apply Hm; eapply step_grows_trans; [eapply step_grows_boundary; eauto |];
           apply step_grows_same; reflexivity | apply Hm, step_grows_refl]
       | apply Hm; rewrite step_run_head_eq; eapply step_grows_trans;
         [apply step_grows_head | apply step_grows_interp]]).
Qed.

Lemma step_grows_iterate : forall R I Sch n s, grows (xs s) (xs (iterate R I Sch n s)).
Proof.
  intros R I Sch n; induction n as [| n IH]; intros s; cbn; [apply step_grows_refl |].
  eapply step_grows_trans; [apply step_grows_step | apply IH].
Qed.
