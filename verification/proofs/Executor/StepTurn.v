(** * Step domain: single steps at a turn boundary, foreign inputs and closing.

    Lemmas for S5, S6, S7 and S11: what one step does when the queue is empty, when a foreign
    input is due, and during closing. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Statements StepInv.
Import ListNotations.
Open Scope Z_scope.

(** ** The shape of a step *)

Lemma step_quiet_boundary : forall R I Sch s, quiet I Sch (xs s) -> queue (xs s) = [] ->
  phase (xs s) <> PDone ->
  xs (step R I Sch s) =
  match at_boundary I Sch (xs s) with
  | Some x' => set_micro (set_progress x' (S (progress (xs s)))) (S (micro (xs s)))
  | None => set_micro (xs s) (S (micro (xs s)))
  end.
Proof.
  intros R I Sch s [H1 [H2 H3]] Q P; rewrite step_xs, H1, H2, H3, Q.
  destruct (phase (xs s)); congruence.
Qed.

Lemma step_foreign : forall R I Sch s fi, phase (xs s) <> PDone ->
  stop_due Sch (xs s) = false -> foreign_due I (xs s) = Some fi ->
  step R I Sch s = {| xs := set_micro (on_foreign (set_fseen (xs s) (Some (progress (xs s))))
                                        fi) (S (micro (xs s)));
                      rs := rs s |}.
Proof.
  intros R I Sch s fi P H1 H2; unfold step; cbv beta zeta; rewrite H1, H2.
  destruct (phase (xs s)); congruence.
Qed.

(** ** Field facts *)

Lemma step_violate_fresh : forall x v, phase x <> PDone -> violated x = false ->
  phase (violate x v) <> POpen /\ trace (violate x v) = trace x ++ [AViolation v].
Proof.
  intros x v P V; unfold violate; rewrite V; split.
  - destruct (phase x) eqn:E.
    + rewrite step_close_open; [discriminate | fields; auto].
    + apply step_close_phase; fields; congruence.
    + congruence.
  - rewrite step_close_trace; reflexivity.
Qed.

Lemma step_issue_trace : forall I x k o s,
  trace (issue I x k o s) = trace x ++ [ACommand (next_cmd x) k o] \/
  trace (issue I x k o s) = trace x ++ [AExit VMismatch].
Proof.
  intros; unfold issue; cbv zeta.
  destruct (nth_error (persisted I) (next_cmd x)); [destruct (cmd_eqb k c) |]; auto.
Qed.

Lemma step_issue_op_trace : forall I x f tok op,
  (exists c k, trace (issue_op I x f tok op) = trace x ++ [ACommand c k (Some (f, tok))]) \/
  In (AExit VMismatch) (trace (issue_op I x f tok op)).
Proof.
  intros; unfold issue_op; destruct op as [kk a | d];
    [| destruct (match d with Millis m => split m | Forever => (max_chunk, Endless) end)];
  match goal with |- context [issue ?I ?x ?k ?o ?s] =>
    destruct (step_issue_trace I x k o s) as [E | E]; rewrite E;
      [left; eauto | right; apply in_or_app; right; left; reflexivity] end.
Qed.

(** ** Cursors *)

Lemma step_close_cursor : forall x c, cursor (close x c) = cursor x.
Proof.
  intros x c; unfold close; destruct (phase x) as [| [k |] |]; try destruct c; reflexivity.
Qed.

Lemma step_violate_cursor : forall x v, cursor (violate x v) = cursor x.
Proof.
  intros x v; unfold violate; destruct (violated x); auto; rewrite step_close_cursor; auto.
Qed.

Lemma step_issue_cursor : forall I x k o s, cursor (issue I x k o s) = cursor x.
Proof.
  intros; unfold issue; cbv zeta.
  destruct (nth_error (persisted I) (next_cmd x)); [destruct (cmd_eqb k c) |]; auto.
Qed.

Lemma step_issue_op_cursor : forall I x f tok op, cursor (issue_op I x f tok op) = cursor x.
Proof.
  intros; unfold issue_op; destruct op as [kk a | d];
    [| destruct (match d with Millis m => split m | Forever => (max_chunk, Endless) end)];
    apply step_issue_cursor.
Qed.

Lemma step_after_sample_cursor : forall I y a, cursor (after_sample I y a) = cursor y.
Proof.
  intros I y a; destruct a; cbn; try reflexivity.
  destruct (link_of _) as [[? ?] |]; [apply step_issue_cursor | reflexivity].
Qed.

Lemma step_apply_sample_cursor : forall x c v a, cursor (apply_sample x c v a) = cursor x.
Proof.
  intros x c v a; destruct (step_apply_sample_cases x c v a) as [E | (a' & l & Ha & E)];
    rewrite E; [apply step_violate_cursor | reflexivity].
Qed.

Lemma step_on_notify_cursor : forall I x s r, cursor (on_notify I x s r) = cursor x.
Proof.
  intros I x s r; unfold on_notify.
  destruct s as [c f tok op k rest | c after | c];
    [destruct op, r | destruct r, after | ]; cbv zeta; try reflexivity;
    try apply step_issue_cursor; try apply step_violate_cursor;
    match goal with |- context [apply_sample ?x ?c ?v ?a] =>
      destruct (phase (apply_sample x c v a));
      rewrite ?step_after_sample_cursor; apply step_apply_sample_cursor end.
Qed.

Lemma step_on_cancel_cursor : forall I x s, cursor (on_cancel I x s) = cursor x.
Proof.
  intros I x s; destruct s as [c f tok op k rest | c after | c];
    [| destruct after |]; cbn; try reflexivity; unfold issue_sample;
    rewrite step_issue_cursor; reflexivity.
Qed.

(** ** Extensions with no command *)

(** [y] has [x]'s cursor and extends [x]'s trace with no command. *)
Definition no_cmd_ext (x y : XState) : Prop :=
  cursor y = cursor x /\ exists suf, trace y = trace x ++ suf /\ commands suf = [].

Lemma step_nce_refl : forall x, no_cmd_ext x x.
Proof. intros x; split; auto; exists []; rewrite app_nil_r; auto. Qed.

Lemma step_nce_trans : forall x y z, no_cmd_ext x y -> no_cmd_ext y z -> no_cmd_ext x z.
Proof.
  intros x y z [C1 [s1 [T1 N1]]] [C2 [s2 [T2 N2]]]; split; [congruence |].
  exists (s1 ++ s2); split; [rewrite T2, T1, app_assoc; auto |].
  unfold commands in *; rewrite flat_map_app, N1, N2; auto.
Qed.

Lemma step_nce_same : forall x y, cursor y = cursor x -> trace y = trace x -> no_cmd_ext x y.
Proof. intros x y C T; split; auto; exists []; rewrite app_nil_r; auto. Qed.

Definition not_command (a : Action) : bool :=
  match a with ACommand _ _ _ => false | _ => true end.

Lemma step_nce_emit : forall x a, not_command a = true -> no_cmd_ext x (emit x a).
Proof.
  intros x a H; split; auto; exists [a]; split; auto; destruct a; try discriminate; auto.
Qed.

Lemma step_nce_close : forall x c, no_cmd_ext x (close x c).
Proof. intros; apply step_nce_same; [apply step_close_cursor | apply step_close_trace]. Qed.

Lemma step_nce_violate : forall x v, no_cmd_ext x (violate x v).
Proof.
  intros x v; unfold violate; destruct (violated x); [apply step_nce_refl |].
  eapply step_nce_trans; [apply (step_nce_emit x (AViolation v)); auto |].
  apply (step_nce_trans _ (set_violated (emit x (AViolation v)) true));
    [apply step_nce_same; reflexivity | apply step_nce_close].
Qed.

Lemma step_on_release_closed : forall x f tok, phase x <> POpen -> on_release x f tok = x.
Proof.
  intros x f tok P; unfold on_release; cbv zeta.
  destruct (phase x) eqn:E; [congruence | |]; cbv iota; rewrite E; reflexivity.
Qed.

Lemma step_on_event_closed : forall I x e, phase x <> POpen ->
  phase (on_event I x e) <> POpen /\ no_cmd_ext x (on_event I x e).
Proof.
  intros I x e P; unfold on_event; destruct (phase x) eqn:E; [congruence | |
    split; [congruence | apply step_nce_refl]].
  destruct e as [f tok op | f tok | pr t | f | r].
  - unfold on_start; rewrite E; split; [fields; congruence |].
    apply (step_nce_trans _ (emit x (AStart f tok op)));
      [apply step_nce_emit; reflexivity | apply step_nce_same; auto].
  - rewrite step_on_release_closed; [split; [congruence | apply step_nce_refl] | congruence].
  - destruct (Nat.eqb pr 0).
    + split; [fields; congruence | apply step_nce_same; auto].
    + split; [apply step_violate_phase; congruence | apply step_nce_violate].
  - split; [fields; congruence | apply step_nce_same; auto].
  - destruct (root_exit x).
    + split; [apply step_violate_phase; congruence | apply step_nce_violate].
    + split; [apply step_close_phase; fields; congruence |].
      apply (step_nce_trans _ (set_root_exit x (Some r)));
        [apply step_nce_same; reflexivity | apply step_nce_close].
Qed.

Lemma step_interp_closed : forall {X} I (s : Script X) x, phase x <> POpen ->
  phase (fst (interp I x s)) <> POpen /\ no_cmd_ext x (fst (interp I x s)).
Proof.
  intros X I s; induction s as [r | e k IH | f k IH | f k IH | f k IH]; intros x P; cbn.
  - split; [exact P | apply step_nce_refl].
  - destruct (step_on_event_closed I x e P) as [P1 N1].
    destruct (IH _ P1) as [P2 N2]; split; [exact P2 | eapply step_nce_trans; eauto].
  - set (y := match phase x with PDone => x | _ => emit x (AClock f (logical x)) end).
    assert (Hy : phase y <> POpen /\ no_cmd_ext x y).
    { unfold y; destruct (phase x) eqn:E; [congruence | |];
        (split; [fields; congruence | try apply step_nce_emit; try apply step_nce_refl]);
        reflexivity. }
    destruct Hy as [P1 N1]; destruct (IH (logical x) _ P1) as [P2 N2]; split; auto.
    eapply step_nce_trans; eauto.
  - set (y := match phase x with
              | PDone => x
              | _ => emit (set_draws x (S (draws x))) (ADraw f (stream I (draws x))) end).
    assert (Hy : phase y <> POpen /\ no_cmd_ext x y).
    { unfold y; destruct (phase x) eqn:E; [congruence | |].
      - split; [fields; congruence |].
        apply (step_nce_trans _ (set_draws x (S (draws x))));
          [apply step_nce_same; reflexivity | apply step_nce_emit; reflexivity].
      - split; [fields; congruence | apply step_nce_refl]. }
    destruct Hy as [P1 N1]; destruct (IH (stream I (draws x)) _ P1) as [P2 N2]; split; auto.
    eapply step_nce_trans; eauto.
  - assert (P1 : phase (set_live x (live x ++ [f])) <> POpen) by (fields; auto).
    destruct (IH (match phase x with PClosing _ => true | _ => false end) _ P1) as [P2 N2];
      split; [exact P2 |].
    apply (step_nce_trans _ (set_live x (live x ++ [f])));
      [apply step_nce_same; reflexivity | exact N2].
Qed.

Lemma step_head_state_closed : forall x t rest,
  phase (head_state x t rest) = phase x /\ no_cmd_ext x (head_state x t rest).
Proof.
  intros x t rest; unfold head_state; cbv zeta.
  assert (H : forall y, phase (match task_action t with Some a => emit y a | None => y end)
                        = phase y /\ no_cmd_ext y (match task_action t with
                                                   Some a => emit y a | None => y end)).
  { intros y; destruct t; cbn; split; auto; try apply step_nce_refl;
      apply step_nce_emit; reflexivity. }
  set (y0 := set_progress (set_queue x rest) (S (progress x))).
  destruct (H y0) as [P1 N1].
  assert (N0 : no_cmd_ext x y0) by (apply step_nce_same; reflexivity).
  revert P1 N1; generalize (match task_action t with Some a => emit y0 a | None => y0 end).
  intros y P1 N1.
  assert (Ny : no_cmd_ext x y) by exact (step_nce_trans _ _ _ N0 N1).
  assert (P2 : phase y = phase x) by (rewrite P1; reflexivity).
  destruct t; try (split; [exact P2 | exact Ny]); destruct (awaiter y);
    try (split; [exact P2 | exact Ny]); destruct (pair_eqb _ _);
    try (split; [exact P2 | exact Ny]);
    (split; [fields; exact P2 | apply (step_nce_trans _ y);
                                [exact Ny | apply step_nce_same; reflexivity]]).
Qed.
