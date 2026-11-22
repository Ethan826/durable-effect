(** * Step domain: S5, S5_exit, S6, S7, S11 and ReleasedSampleUnreachable. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Statements Obligations StepInv StepTurn.
Import ListNotations.
Open Scope Z_scope.

(** ** S5 *)

Theorem step_s5 : S5.
Proof.
  intros R p I Sch s g _ P V Stop F; cbv zeta.
  assert (Hf : exists fi, foreign_due I (xs s) = Some fi /\
                 (fi = FResume g \/ fi = FInterrupt g)) by
    (destruct F as [F | F]; eexists; split; eauto).
  destruct Hf as [fi [Hfi Hk]].
  rewrite (step_foreign R I Sch s fi P Stop Hfi); cbn [xs rs].
  split; [reflexivity |].
  assert (P' : phase (set_fseen (xs s) (Some (progress (xs s)))) <> PDone) by (fields; auto).
  assert (V' : violated (set_fseen (xs s) (Some (progress (xs s)))) = false) by (fields; auto).
  destruct Hk as [-> | ->]; cbn [on_foreign];
    match goal with |- context [violate ?y ?v] =>
      destruct (step_violate_fresh y v P' V') as [Hp Ht];
      split; [exists v; fields; rewrite Ht; reflexivity | fields; exact Hp] end.
Qed.

Theorem step_s5_exit : S5_exit.
Proof.
  intros R _ p I Sch n v w Hv Hw; unfold run in *.
  pose proof (step_inv_iterate R I Sch n (initial R p I) (step_inv_initial R p I)) as HI.
  exact (inv_exit_defect _ HI w v Hw Hv).
Qed.

(** ** S6 *)

Theorem step_s6 : S6.
Proof.
  intros R p I Sch s Hr Hq Q; cbv zeta.
  pose proof (step_inv_reachable R p I Sch s Hr) as HI.
  assert (Hb : forall x', at_boundary I Sch (xs s) = Some x' -> phase (xs s) <> PDone ->
            xs (step R I Sch s) = set_micro (set_progress x' (S (progress (xs s))))
                                            (S (micro (xs s)))).
  { intros x' E P; rewrite (step_quiet_boundary R I Sch s Hq Q P), E; reflexivity. }
  assert (Hv : phase (xs s) = POpen -> violated (xs s) = false).
  { intros P; destruct (violated (xs s)) eqn:V; auto; exfalso; exact (inv_viol _ HI V P). }
  split; [| split; [| split; [| split]]].
  - intros P S0 W.
    assert (E : at_boundary I Sch (xs s) = Some (violate (xs s) Blocked)).
    { unfold at_boundary; rewrite P, W, S0; destruct (held (xs s)); reflexivity. }
    rewrite (Hb _ E) by congruence; fields.
    exact (proj2 (step_violate_open _ _ P (Hv P))).
  - intros P sb S0 N A.
    assert (E : at_boundary I Sch (xs s) = None).
    { unfold at_boundary; rewrite P.
      assert (Hs : at_boundary_sub I Sch (xs s) sb = None).
      { unfold at_boundary_sub; apply Nat.leb_le in A; rewrite A; reflexivity. }
      destruct (held (xs s)) eqn:H, (waiter (xs s)) as [[[f tok] op] |] eqn:W;
        try (exfalso; apply N; split; congruence); rewrite S0; exact Hs. }
    rewrite (step_quiet_boundary R I Sch s Hq Q) by congruence; rewrite E; fields; auto.
  - intros P H S0 f tok op W.
    assert (E : at_boundary I Sch (xs s) =
                Some (issue_op I (set_waiter (xs s) None) f tok op)).
    { unfold at_boundary; rewrite P, H, W, S0; reflexivity. }
    rewrite (Hb _ E) by congruence; fields.
    destruct (step_issue_op_trace I (set_waiter (xs s) None) f tok op) as [[c [k T]] | T].
    + left; exists c, k; exact T.
    + right; exact T.
  - intros P H f tok op W.
    assert (E : at_boundary I Sch (xs s) =
                Some (enqueue (set_waiter (set_held (xs s) false) None) (DeliverCancel f tok))).
    { unfold at_boundary; rewrite P, H, W; reflexivity. }
    rewrite (Hb _ E) by congruence; fields; rewrite Q; reflexivity.
  - intros c P.
    assert (E : at_boundary I Sch (xs s) = Some (finish (xs s) (verdict (xs s)))).
    { unfold at_boundary; rewrite P; reflexivity. }
    rewrite (Hb _ E) by congruence; reflexivity.
Qed.

(** ** S7 *)

Lemma step_boundary_sub_cursor : forall I Sch x s y, at_boundary_sub I Sch x s = Some y ->
  cursor y = S (cursor x).
Proof.
  intros I Sch x s y E; unfold at_boundary_sub in E.
  destruct (arrived Sch (micro x) <=? cursor x)%nat; [discriminate |].
  destruct (nth_error (entries I) (cursor x)) as [[c r |] |]; [| | discriminate].
  - destruct (Nat.eqb c (sub_cmd s)).
    + inversion E; subst; rewrite step_on_notify_cursor; reflexivity.
    + destruct (c <? next_cmd x)%nat; inversion E; subst; reflexivity.
  - inversion E; subst; rewrite step_on_cancel_cursor; reflexivity.
Qed.

Theorem step_s7 : S7.
Proof.
  intros R p I Sch s _ Hq Q P; cbv zeta.
  rewrite (step_quiet_boundary R I Sch s Hq Q) by congruence.
  unfold at_boundary; rewrite P.
  destruct (held (xs s)) eqn:H, (waiter (xs s)) as [[[f tok] op] |] eqn:W.
  - fields; split; [lia | split; [auto |]].
    intros sb _ N; exfalso; apply N; split; congruence.
  - destruct (sub (xs s)) as [sb |] eqn:S0.
    + destruct (at_boundary_sub I Sch (xs s) sb) as [y |] eqn:E.
      * fields; rewrite (step_boundary_sub_cursor _ _ _ _ _ E).
        split; [lia | split].
        -- intros [[_ C] | C]; [congruence | discriminate].
        -- intros sb' Hsb _ _ _; inversion Hsb; subst; reflexivity.
      * fields; split; [lia | split; [auto |]].
        intros sb' Hsb _ A En; inversion Hsb; subst.
        unfold at_boundary_sub in E; apply Nat.leb_gt in A; rewrite A in E.
        destruct En as [En | [r En]]; rewrite En in E; [discriminate |].
        rewrite Nat.eqb_refl in E; discriminate.
    + fields; rewrite step_violate_cursor; split; [lia | split; [auto |]].
      intros sb' Hsb; discriminate.
  - destruct (sub (xs s)) as [sb |] eqn:S0.
    + destruct (at_boundary_sub I Sch (xs s) sb) as [y |] eqn:E.
      * fields; rewrite (step_boundary_sub_cursor _ _ _ _ _ E).
        split; [lia | split].
        -- intros [[C _] | C]; [congruence | discriminate].
        -- intros sb' Hsb _ _ _; inversion Hsb; subst; reflexivity.
      * fields; split; [lia | split; [auto |]].
        intros sb' Hsb _ A En; inversion Hsb; subst.
        unfold at_boundary_sub in E; apply Nat.leb_gt in A; rewrite A in E.
        destruct En as [En | [r En]]; rewrite En in E; [discriminate |].
        rewrite Nat.eqb_refl in E; discriminate.
    + fields; rewrite step_issue_op_cursor; fields; split; [lia | split; [auto |]].
      intros sb' Hsb; discriminate.
  - destruct (sub (xs s)) as [sb |] eqn:S0.
    + destruct (at_boundary_sub I Sch (xs s) sb) as [y |] eqn:E.
      * fields; rewrite (step_boundary_sub_cursor _ _ _ _ _ E).
        split; [lia | split].
        -- intros [[C _] | C]; [congruence | discriminate].
        -- intros sb' Hsb _ _ _; inversion Hsb; subst; reflexivity.
      * fields; split; [lia | split; [auto |]].
        intros sb' Hsb _ A En; inversion Hsb; subst.
        unfold at_boundary_sub in E; apply Nat.leb_gt in A; rewrite A in E.
        destruct En as [En | [r En]]; rewrite En in E; [discriminate |].
        rewrite Nat.eqb_refl in E; discriminate.
    + fields; rewrite step_violate_cursor; split; [lia | split; [auto |]].
      intros sb' Hsb; discriminate.
Qed.

(** ** S11 *)

Lemma step_closing_step : forall R I Sch s cut, phase (xs s) = PClosing cut ->
  no_cmd_ext (xs s) (xs (step R I Sch s)).
Proof.
  intros R I Sch s cut P; rewrite step_xs, P.
  assert (Hm : forall y z, no_cmd_ext y z -> no_cmd_ext y (set_micro z (S (micro (xs s)))))
    by (intros y z [C [suf [T N]]]; split; auto; exists suf; auto).
  destruct (stop_due Sch (xs s));
    [apply Hm, step_nce_same; reflexivity |].
  destruct (foreign_due I (xs s)) as [fi |].
  { apply Hm; apply (step_nce_trans _ (set_fseen (xs s) (Some (progress (xs s)))));
      [apply step_nce_same; reflexivity |].
    destruct fi; cbn [on_foreign]; try apply step_nce_violate; apply step_nce_refl. }
  destruct (cut_due Sch (xs s)) as [k |].
  { apply Hm; unfold on_cut; apply (step_nce_trans _ (emit (xs s) (ACut k)));
      [apply step_nce_emit; reflexivity |].
    destruct k; [apply step_nce_close | apply step_nce_close | apply step_nce_same; auto]. }
  destruct (queue (xs s)) as [| t rest].
  - unfold at_boundary; rewrite P; apply Hm.
    apply (step_nce_trans _ (finish (xs s) (verdict (xs s))));
      [| apply step_nce_same; reflexivity].
    unfold finish; apply (step_nce_trans _ (emit (xs s) (AExit (verdict (xs s)))));
      [apply step_nce_emit; reflexivity | apply step_nce_same; reflexivity].
  - apply Hm; rewrite step_run_head_eq.
    destruct (step_head_state_closed (xs s) t rest) as [P1 N1].
    assert (P2 : phase (head_state (xs s) t rest) <> POpen) by congruence.
    destruct (step_interp_closed I (run_task R (rs s) t) _ P2) as [_ N2].
    exact (step_nce_trans _ _ _ N1 N2).
Qed.

Theorem step_s11 : S11.
Proof.
  split; [| split].
  - intros R p I Sch s sb Hr _ S0; exact (inv_cmd _ (step_inv_reachable R p I Sch s Hr) sb S0).
  - intros R p I Sch s sb c r _ Hq Q P S0 N A En Hc.
    rewrite (step_quiet_boundary R I Sch s Hq Q) by congruence.
    assert (E : at_boundary I Sch (xs s) = at_boundary_sub I Sch (xs s) sb).
    { unfold at_boundary; rewrite P.
      destruct (held (xs s)) eqn:H, (waiter (xs s)) as [[[f tok] op] |] eqn:W;
        try (exfalso; apply N; split; congruence); rewrite S0; reflexivity. }
    rewrite E; unfold at_boundary_sub.
    apply Nat.leb_gt in A; rewrite A, En.
    apply Nat.eqb_neq in Hc; rewrite Hc.
    destruct (c <? next_cmd (xs s))%nat; reflexivity.
  - intros R p I Sch s cut _ P; cbv zeta.
    destruct (step_closing_step R I Sch s cut P) as [C [suf [T N]]].
    split; [exact C | exists suf; auto].
Qed.

(** ** The obligation about released samples *)

Theorem step_released_sample_unreachable : ReleasedSampleUnreachable.
Proof.
  intros R p I Sch s Hr c f tok k E.
  pose proof (inv_released _ (step_inv_reachable R p I Sch s Hr)) as H.
  rewrite E in H; discriminate.
Qed.
