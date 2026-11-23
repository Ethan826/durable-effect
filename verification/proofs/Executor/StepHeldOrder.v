(** * Step domain: [HeldCancelDeliveredFirst], X5 in its order.

    Adapted from the second independent review's scratch proof (its finding 1): the
    induction of StepHeldRun.v with a conclusion that keeps the order of the delivered
    cancellation and later commands. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Statements Obligations StepInv StepTurn StepLog
  StepAwait StepAwaitTurn StepGrow StepHeldRun.
Import ListNotations.
Open Scope Z_scope.

Lemma step_strong_hc_step : forall R I Sch s L, Inv (xs s) -> SInv L (xs s) ->
  NoDup (start_tokens (L ++ fst (step_log R I Sch s))) ->
  phase (xs (step R I Sch s)) = POpen -> hc (xs s) ->
  exists suf, trace (xs (step R I Sch s)) = trace (xs s) ++ suf /\
    ((exists f tok rest, suf = ACancelled f tok :: rest) \/
     (no_kop suf /\ hc (xs (step R I Sch s)))).
Proof.
  intros R I Sch s L HI SI Hnd Py H.
  assert (P : phase (xs s) = POpen).
  { destruct (phase (xs s)) eqn:E; auto; exfalso; revert Py;
      apply step_closed_step; congruence. }
  destruct (SI P) as [AI HH].
  assert (Hm : forall y, hc_ext (xs s) y ->
     exists suf, trace (set_micro y (S (micro (xs s)))) = trace (xs s) ++ suf /\
       ((exists f tok rest, suf = ACancelled f tok :: rest) \/
        (no_kop suf /\ hc (set_micro y (S (micro (xs s))))))).
  { intros y [suf [T [N Hc]]]; exists suf; split; [exact T | right; split; auto]. }
  unfold step_log in Hnd; rewrite step_xs in *; rewrite P in *.
  destruct (stop_due Sch (xs s)); [fields; discriminate |].
  destruct (foreign_due I (xs s)) as [fi |].
  { apply Hm; fields.
    assert (Hf : hc_ext (xs s) (set_fseen (xs s) (Some (progress (xs s)))))
      by (apply step_hc_ext_same; auto).
    destruct fi; cbn [on_foreign] in *; try rewrite (step_violate_stays _ _ Py); exact Hf. }
  destruct (cut_due Sch (xs s)) as [k |].
  { exfalso; fields; unfold on_cut in Py.
    destruct k; try (rewrite step_close_open in Py; [discriminate | fields; auto]).
    fields; discriminate. }
  destruct (queue (xs s)) as [| t rest] eqn:Q.
  - destruct (at_boundary I Sch (xs s)) as [y |] eqn:E.
    + apply Hm; fields.
      assert (Hy : hc_ext (xs s) y) by (eapply step_hc_boundary; eauto).
      destruct Hy as [suf [T [N Hc]]]; exists suf; auto.
    + apply Hm, step_hc_ext_same; auto.
  - rewrite step_run_head_eq in *; fields; cbn [fst] in Hnd.
    destruct (step_task_cases t) as [[f [tok Et]] | Nt].
    + (* The queued cancellation runs: [ACancelled] is recorded. *)
      subst t.
      destruct (step_grows_interp I (run_task R (rs s) (DeliverCancel f tok))
                  (head_state (xs s) (DeliverCancel f tok) rest)) as [suf T].
      rewrite step_head_cancel_trace in T.
      exists (ACancelled f tok :: suf); fields; rewrite T, <- app_assoc; split; auto.
      left; exists f, tok, suf; reflexivity.
    + replace (L ++ LTask t :: ilog I (head_state (xs s) t rest) (run_task R (rs s) t))
        with ((L ++ [LTask t]) ++ ilog I (head_state (xs s) t rest) (run_task R (rs s) t))
        in * by (rewrite <- app_assoc; reflexivity).
      assert (Hh : hc_ext (xs s) (head_state (xs s) t rest)) by (apply step_hc_head; auto).
      assert (Hi : hc_ext (head_state (xs s) t rest)
                     (fst (interp I (head_state (xs s) t rest) (run_task R (rs s) t)))).
      { apply (step_hc_interp _ _ _ (L ++ [LTask t])); auto.
        - apply step_head_state_iinv; auto.
        - apply step_sinv_head; auto.
        - destruct Hh as [_ [_ [_ Hc]]]; exact Hc. }
      destruct (step_hc_ext_trans _ _ _ Hh Hi) as [suf [T [N Hc]]].
      exists suf; split; [exact T | right; auto].
Qed.


Lemma step_before_cancel_nokop : forall suf, no_kop suf -> before_cancel suf.
Proof.
  intros suf N pre c op o post E; exfalso; apply (N c op o); rewrite E.
  apply in_or_app; right; left; reflexivity.
Qed.

Lemma step_before_cancel_head : forall f tok rest, before_cancel (ACancelled f tok :: rest).
Proof.
  intros f tok rest pre c op o post E; destruct pre as [| a pre]; [discriminate |].
  injection E as Ea _; subst a; exists f, tok; left; reflexivity.
Qed.

Lemma step_list_eq_dec_app : forall (a b pre : list Action) c op o post,
  a ++ b = pre ++ ACommand c (KOp op) o :: post ->
  (exists pre2, pre = a ++ pre2 /\ b = pre2 ++ ACommand c (KOp op) o :: post) \/
  In (ACommand c (KOp op) o) a.
Proof.
  induction a as [| x a IH]; intros b pre c op o post E.
  - left; exists pre; split; [reflexivity | exact E].
  - destruct pre as [| y pre].
    + injection E as Ex _; subst x; right; left; reflexivity.
    + injection E as Exy E'; subst y.
      destruct (IH b pre c op o post E') as [[pre2 [E1 E2]] | Hin].
      * left; exists pre2; rewrite E1; split; [reflexivity | exact E2].
      * right; right; exact Hin.
Qed.

Lemma step_before_cancel_app : forall a b, no_kop a -> before_cancel b -> before_cancel (a ++ b).
Proof.
  intros a b Na Bb pre c op o post E.
  destruct (step_list_eq_dec_app a b pre c op o post E) as [[pre2 [E1 E2]] | Hin].
  - destruct (Bb pre2 c op o post E2) as [f [tok Hin]]; exists f, tok; rewrite E1;
      apply in_or_app; right; exact Hin.
  - exfalso; exact (Na c op o Hin).
Qed.

Lemma step_strong_hc_run : forall R I Sch j s L, Inv (xs s) -> SInv L (xs s) ->
  NoDup (start_tokens (L ++ fst (elog R I Sch j s))) ->
  phase (xs (iterate R I Sch j s)) = POpen -> hc (xs s) ->
  exists suf, trace (xs (iterate R I Sch j s)) = trace (xs s) ++ suf /\ before_cancel suf.
Proof.
  intros R I Sch j; induction j as [| j IH]; intros s L HI SI Hnd Py H.
  - exists []; rewrite app_nil_r; split; [reflexivity | apply step_before_cancel_nokop, step_no_kop_nil].
  - cbn [iterate] in *; rewrite step_elog_fst, app_assoc in Hnd.
    assert (Ps : phase (xs (step R I Sch s)) = POpen).
    { destruct (phase (xs (step R I Sch s))) eqn:E; auto; exfalso; revert Py;
        apply step_closed_iterate; congruence. }
    assert (Hnd1 : NoDup (start_tokens (L ++ fst (step_log R I Sch s))))
      by (rewrite step_start_tokens_app in Hnd; apply NoDup_app_remove_r in Hnd; exact Hnd).
    destruct (step_strong_hc_step R I Sch s L HI SI Hnd1 Ps H) as [s1 [T1 [[f [tok [rest E1]]] | [N1 H1]]]].
    + destruct (step_grows_iterate R I Sch j (step R I Sch s)) as [s2 T2].
      exists (s1 ++ s2); rewrite T2, T1, app_assoc; split; [reflexivity |].
      subst s1; cbn [app]; apply step_before_cancel_head.
    + destruct (IH (step R I Sch s) (L ++ fst (step_log R I Sch s))) as [s2 [T2 C2]];
        auto using step_inv_step, step_sinv_step.
      exists (s1 ++ s2); rewrite T2, T1, app_assoc; split; [reflexivity |].
      apply step_before_cancel_app; auto.
Qed.

(** The stronger form: no durable command precedes the first delivered cancellation. *)
Theorem step_held_cancel_delivered_first : HeldCancelDeliveredFirst.
Proof.
  intros R HM p I Sch n m x y Px Hx Py.
  set (s0 := initial R p I) in *.
  destruct HM as [_ [[_ Hnd] _]].
  set (Lg := elog R I Sch (n + m) s0).
  specialize (Hnd p (seed I) (answers_of (fst Lg)) (snd Lg)).
  pose proof (step_open_log_is_drive R I Sch (n + m) s0 Py) as Hd; cbv zeta in Hd.
  change (rs s0) with (init R p (seed I)) in Hd; fold Lg in Hd.
  rewrite Hd in Hnd; unfold Lg in Hnd; rewrite step_elog_add in Hnd.
  assert (Hn : NoDup (start_tokens ([] ++ fst (elog R I Sch n s0))))
    by (rewrite step_start_tokens_app in Hnd; apply NoDup_app_remove_r in Hnd; exact Hnd).
  pose proof (step_sinv_iterate R I Sch n s0 [] (step_inv_initial R p I)
                (step_sinv_initial R p I) Hn) as SI.
  unfold y in Py; rewrite step_iterate_add in Py.
  destruct (step_strong_hc_run R I Sch m (iterate R I Sch n s0) (fst (elog R I Sch n s0)))
    as [suf [T C]]; auto.
  - apply step_inv_iterate, step_inv_initial.
  - left; exact Hx.
  - unfold y; rewrite step_iterate_add, T; fold x; rewrite step_skipn_app; exact C.
Qed.
