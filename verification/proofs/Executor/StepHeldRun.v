(** * Step domain: a held cancellation is delivered before any durable command.

    While the attempt is open, a cancellation is either held or queued as a [DeliverCancel]
    ([hc]). Under I4 a queued cancellation belongs to the awaiter and is the only delivery
    for that await ([HInv]), so nothing can issue an operation while it is queued: a start
    finds the awaiter set and is a violation. It leaves the queue only by running, which
    records [ACancelled], or by its fiber's release, which holds it again. A held
    cancellation goes to the next fiber that starts, and a turn boundary issues only a
    sample while one is held. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Statements Obligations StepInv StepTurn StepLog
  StepAwait StepAwaitTurn StepGrow.
Import ListNotations.
Open Scope Z_scope.

Definition hc (x : XState) : Prop :=
  held x = true \/ exists f tok, In (DeliverCancel f tok) (queue x).

Definition no_kop (suf : list Action) : Prop := forall c op o, ~ In (ACommand c (KOp op) o) suf.

Definition cancelled (suf : list Action) : Prop := exists f tok, In (ACancelled f tok) suf.

(** [y] extends [x]'s trace with no durable command, and a cancellation is still pending. *)
Definition hc_ext (x y : XState) : Prop :=
  exists suf, trace y = trace x ++ suf /\ no_kop suf /\ hc y.

Lemma step_no_kop_app : forall a b, no_kop a -> no_kop b -> no_kop (a ++ b).
Proof.
  intros a b Ha Hb c op o H; apply in_app_or in H; destruct H; [eapply Ha | eapply Hb]; eauto.
Qed.

Lemma step_hc_ext_trans : forall x y z, hc_ext x y -> hc_ext y z -> hc_ext x z.
Proof.
  intros x y z [s1 [T1 [N1 _]]] [s2 [T2 [N2 H2]]]; exists (s1 ++ s2).
  rewrite T2, T1, app_assoc; split; [reflexivity | split; [apply step_no_kop_app |]]; auto.
Qed.

(** One appended action that is not a durable command, with the pending cancellation kept. *)
Lemma step_hc_ext_by : forall x y suf, trace y = trace x ++ suf -> no_kop suf -> hc y ->
  hc_ext x y.
Proof. intros x y suf T N H; exists suf; auto. Qed.

Lemma step_no_kop_nil : no_kop [].
Proof. intros c op o []. Qed.

Lemma step_no_kop_one : forall a, (forall c op o, a <> ACommand c (KOp op) o) -> no_kop [a].
Proof. intros a H c op o [E | []]; exact (H c op o E). Qed.

Lemma step_hc_same : forall x y, hc x -> held y = held x ->
  (forall f tok, In (DeliverCancel f tok) (queue x) -> In (DeliverCancel f tok) (queue y)) ->
  hc y.
Proof.
  intros x y [H | [f [tok H]]] Hh Hq; [left; congruence | right; exists f, tok; auto].
Qed.

Lemma step_hc_ext_same : forall x y, trace y = trace x -> hc x -> held y = held x ->
  (forall f tok, In (DeliverCancel f tok) (queue x) -> In (DeliverCancel f tok) (queue y)) ->
  hc_ext x y.
Proof.
  intros x y T H Hh Hq; exists []; rewrite T, app_nil_r; split; auto;
    split; [apply step_no_kop_nil | eapply step_hc_same; eauto].
Qed.

Lemma step_hc_ext_emit : forall x a, (forall c op o, a <> ACommand c (KOp op) o) -> hc x ->
  hc_ext x (emit x a).
Proof.
  intros x a Ha H; exists [a]; split; [reflexivity | split; [apply step_no_kop_one; auto |]].
  apply (step_hc_same x); auto.
Qed.

(** ** Events *)

Lemma step_release_rest_fields : forall y f tok,
  held (release_rest y f tok) = held y /\ queue (release_rest y f tok) = queue y /\
  trace (release_rest y f tok) = trace y.
Proof.
  intros y f tok; unfold release_rest.
  destruct (phase y); auto; destruct (awaiter y); auto; destruct (negb _); auto.
  cbv zeta; destruct (waiter y); auto; destruct (sub y); auto.
  destruct (release_sub _) as [[[? ?] ?] |]; auto; destruct (pair_eqb _ _); auto.
Qed.

Lemma step_hc_release : forall x f tok, phase x = POpen -> hc x ->
  hc_ext x (on_release x f tok).
Proof.
  intros x f tok P H; rewrite step_on_release_split.
  destruct (step_release_rest_fields (release_pre x f tok) f tok) as [Hh [Hq Ht]].
  destruct (step_release_pre_fields x f tok) as (_ & _ & _ & _ & T & _).
  exists []; rewrite Ht, T, app_nil_r; split; [reflexivity | split; [apply step_no_kop_nil |]].
  unfold hc; rewrite Hh, Hq; unfold release_pre; rewrite P; cbv zeta.
  destruct (dropped_cancel x f tok) eqn:D; [left; reflexivity |].
  destruct H as [H | [g [tk H]]]; [left; exact H | right; exists g, tk]; fields.
  apply filter_In; split; auto.
  apply step_dropped_false in D; cbn.
  destruct (Nat.eqb f g && Nat.eqb tok tk) eqn:E; auto.
  apply andb_true_iff in E; destruct E as [E1 E2]; apply Nat.eqb_eq in E1;
    apply Nat.eqb_eq in E2; subst; contradiction.
Qed.

Lemma step_hc_start : forall I x f tok op, phase x = POpen -> HInv x -> hc x ->
  phase (on_start I x f tok op) = POpen -> hc_ext x (on_start I x f tok op).
Proof.
  intros I x f tok op P HH H Py.
  assert (He : hc_ext x (emit x (AStart f tok op))) by (apply step_hc_ext_emit; auto; discriminate).
  unfold on_start in *; rewrite P in *; cbv zeta in *.
  destruct (zero_sleep op).
  - eapply step_hc_ext_trans; [exact He |].
    apply step_hc_ext_same; [reflexivity | destruct He as [_ [_ [_ Hc]]]; exact Hc |
                             reflexivity | intros g tk Hin; fields; apply in_or_app; auto].
  - fields; destruct (awaiter x) as [a |] eqn:Ea.
    + rewrite (step_violate_stays _ _ Py); exact He.
    + (* No cancellation is queued without an awaiter, so one is held. *)
      assert (Hh : held x = true).
      { destruct H as [H | [g [tk Hin]]]; auto.
        destruct (h_dc _ HH g tk Hin) as [A _]; congruence. }
      rewrite Hh; exists [AStart f tok op]; fields; split; [reflexivity |].
      split; [apply step_no_kop_one; discriminate |].
      right; exists f, tok; apply in_or_app; right; left; reflexivity.
Qed.

Lemma step_hc_event : forall I x e, phase x = POpen -> HInv x -> hc x ->
  phase (on_event I x e) = POpen -> hc_ext x (on_event I x e).
Proof.
  intros I x e P HH H Py; unfold on_event in *; rewrite P in *.
  destruct e as [f tok op | f tok | pr t | f | r].
  - apply step_hc_start; auto.
  - apply step_hc_release; auto.
  - destruct (Nat.eqb pr 0).
    + apply step_hc_ext_same; auto; intros g tk Hin; fields; apply in_or_app; auto.
    + rewrite (step_violate_stays _ _ Py); apply step_hc_ext_same; auto.
  - apply step_hc_ext_same; fields; auto.
  - destruct (root_exit x).
    + rewrite (step_violate_stays _ _ Py); apply step_hc_ext_same; auto.
    + rewrite (step_close_stays _ _ Py); apply step_hc_ext_same; fields; auto.
Qed.

(** ** Inside a task *)

Lemma step_hc_interp : forall {X} I (s : Script X) x L, IInv x -> SInv L x ->
  NoDup (start_tokens (L ++ ilog I x s)) -> hc x ->
  phase (fst (interp I x s)) = POpen -> hc_ext x (fst (interp I x s)).
Proof.
  intros X I s; induction s as [r | e k IH | f k IH | f k IH | f k IH];
    intros x L HI SI Hnd H Py; cbn [ilog interp fst] in *.
  - apply step_hc_ext_same; auto.
  - assert (Pe : phase (on_event I x e) = POpen).
    { destruct (phase (on_event I x e)) eqn:E; auto; exfalso; revert Py;
        apply step_interp_closed; congruence. }
    assert (P : phase x = POpen).
    { destruct (phase x) eqn:E; auto; exfalso; revert Pe;
        apply step_on_event_closed; congruence. }
    destruct (SI P) as [AI HH].
    assert (He : hc_ext x (on_event I x e)) by (apply step_hc_event; auto).
    replace (L ++ LEvent e :: ilog I (on_event I x e) k)
      with ((L ++ [LEvent e]) ++ ilog I (on_event I x e) k) in *
      by (rewrite <- app_assoc; reflexivity).
    eapply step_hc_ext_trans; [exact He |].
    apply (IH _ (L ++ [LEvent e])); auto using step_on_event_iinv.
    + apply step_sinv_event; auto.
      rewrite step_start_tokens_app in Hnd; apply NoDup_app_remove_r in Hnd; exact Hnd.
    + destruct He as [_ [_ [_ Hc]]]; exact Hc.
  - set (y := match phase x with PDone => x | _ => emit x (AClock f (logical x)) end) in *.
    replace (L ++ LClock f (logical x) :: ilog I y (k (logical x)))
      with ((L ++ [LClock f (logical x)]) ++ ilog I y (k (logical x))) in *
      by (rewrite <- app_assoc; reflexivity).
    assert (Hy : hc_ext x y)
      by (unfold y; destruct (phase x); [apply step_hc_ext_emit | apply step_hc_ext_emit |
                                         apply step_hc_ext_same]; auto; discriminate).
    eapply step_hc_ext_trans; [exact Hy |].
    apply (IH _ _ (L ++ [LClock f (logical x)])); auto.
    + unfold y; destruct (phase x); auto; apply step_iinv_emit; auto.
    + apply (step_sinv_mono L); [| intros; apply step_mono_app; auto].
      unfold y; destruct (phase x) eqn:P; auto;
        apply (step_sinv_same _ x); fields; auto.
    + destruct Hy as [_ [_ [_ Hc]]]; exact Hc.
  - set (y := match phase x with
              | PDone => x
              | _ => emit (set_draws x (S (draws x))) (ADraw f (stream I (draws x))) end) in *.
    replace (L ++ LDraw f (stream I (draws x)) :: ilog I y (k (stream I (draws x))))
      with ((L ++ [LDraw f (stream I (draws x))]) ++ ilog I y (k (stream I (draws x)))) in *
      by (rewrite <- app_assoc; reflexivity).
    assert (Hy : hc_ext x y).
    { unfold y; destruct (phase x); try (apply step_hc_ext_same; auto; fail);
        (exists [ADraw f (stream I (draws x))]; split; [reflexivity |];
         split; [apply step_no_kop_one; discriminate | apply (step_hc_same x); auto]). }
    eapply step_hc_ext_trans; [exact Hy |].
    apply (IH _ _ (L ++ [LDraw f (stream I (draws x))])); auto.
    + unfold y; destruct (phase x); auto; apply step_iinv_emit; auto;
        apply step_iinv_set_draws; auto.
    + apply (step_sinv_mono L); [| intros; apply step_mono_app; auto].
      unfold y; destruct (phase x) eqn:P; auto;
        apply (step_sinv_same _ x); fields; auto.
    + destruct Hy as [_ [_ [_ Hc]]]; exact Hc.
  - set (b := match phase x with PClosing _ => true | _ => false end) in *.
    set (y := match phase x with PDone => x | _ => emit x (ARegister f) end) in *.
    replace (L ++ LRegister f b :: ilog I (set_live y (live y ++ [f])) (k b))
      with ((L ++ [LRegister f b]) ++ ilog I (set_live y (live y ++ [f])) (k b)) in *
      by (rewrite <- app_assoc; reflexivity).
    assert (HY : IInv y) by (unfold y; destruct (phase x); auto; apply step_iinv_emit; auto).
    assert (SY : SInv L y)
      by (unfold y; destruct (phase x) eqn:P; auto; apply (step_sinv_same _ x); fields; auto).
    assert (Hy : hc_ext x (set_live y (live y ++ [f]))).
    { eapply step_hc_ext_trans with (y := y).
      - unfold y; destruct (phase x); [apply step_hc_ext_emit | apply step_hc_ext_emit |
                                       apply step_hc_ext_same]; auto; discriminate.
      - assert (Hcy : hc y)
          by (unfold y; destruct (phase x); auto; apply (step_hc_same x); auto).
        apply step_hc_ext_same; auto. }
    eapply step_hc_ext_trans; [exact Hy |].
    apply (IH _ _ (L ++ [LRegister f b])); auto.
    + destruct HY as [H1 H2]; split; [apply step_inv_set_live |]; auto.
    + apply (step_sinv_mono L); [| intros; apply step_mono_app; auto].
      apply (step_sinv_same _ y); fields; auto.
    + destruct Hy as [_ [_ [_ Hc]]]; exact Hc.
Qed.

(** ** One step *)

Lemma step_head_fields : forall x t rest,
  held (head_state x t rest) = held x /\ queue (head_state x t rest) = rest.
Proof.
  intros x t rest; unfold head_state; cbv zeta; destruct t; cbn;
    try (destruct (awaiter x); try destruct (pair_eqb _ _)); auto.
Qed.

Lemma step_head_cancel_trace : forall x f tok rest,
  trace (head_state x (DeliverCancel f tok) rest) = trace x ++ [ACancelled f tok].
Proof.
  intros; unfold head_state; cbv zeta; cbn; destruct (awaiter x);
    try destruct (pair_eqb _ _); reflexivity.
Qed.

Lemma step_commands_no_kop : forall suf, commands suf = [] -> no_kop suf.
Proof.
  intros suf H c op o Hin; unfold commands in H.
  apply (in_split _ _) in Hin; destruct Hin as [l1 [l2 E]]; subst.
  rewrite flat_map_app in H; cbn in H; destruct (flat_map _ l1); discriminate.
Qed.

Lemma step_hc_head : forall x t rest, queue x = t :: rest ->
  (forall f tok, t <> DeliverCancel f tok) -> hc x -> hc_ext x (head_state x t rest).
Proof.
  intros x t rest Q Nt H.
  destruct (step_head_state_closed x t rest) as [_ [_ [suf [T N]]]].
  destruct (step_head_fields x t rest) as [Hh Hq].
  exists suf; split; [exact T | split; [apply step_commands_no_kop; exact N |]].
  destruct H as [H | [f [tok Hin]]]; [left; congruence | right; exists f, tok].
  rewrite Hq; rewrite Q in Hin; destruct Hin as [E | Hin]; auto.
  exfalso; exact (Nt f tok E).
Qed.

Lemma step_apply_sample_sampled : forall x c s after,
  apply_sample x c s after = violate x Overflow \/
  exists s' l cr l', apply_sample x c s after =
                     set_sub (set_logical (emit x (ASampled c s' l cr)) l') None.
Proof.
  intros; unfold apply_sample; cbv zeta; destruct (max_safe <? _); [left; reflexivity |].
  right; do 4 eexists; reflexivity.
Qed.

Lemma step_hc_boundary : forall I Sch x y, HInv x -> phase x = POpen -> queue x = [] ->
  hc x -> at_boundary I Sch x = Some y -> phase y = POpen -> hc_ext x y.
Proof.
  intros I Sch x y HH P Q H E Py.
  assert (Hh : held x = true)
    by (destruct H as [H | [f [tok Hin]]]; auto; rewrite Q in Hin; contradiction).
  assert (Hc : hc x) by exact H.
  unfold at_boundary in E; rewrite P, Hh in E.
  destruct (waiter x) as [[[f tok] op] |] eqn:W.
  - inversion E; subst; exists []; fields; rewrite app_nil_r.
    split; [reflexivity | split; [apply step_no_kop_nil |]].
    right; exists f, tok; apply in_or_app; right; left; reflexivity.
  - destruct (sub x) as [s |] eqn:S0;
      [| inversion E; subst; rewrite (step_violate_stays _ _ Py); apply step_hc_ext_same; auto].
    destruct (h_held _ HH Hh) as [S1 | [c S1]]; rewrite S0 in S1; [discriminate |].
    inversion S1; subst s; clear S1.
    unfold at_boundary_sub in E.
    destruct (arrived Sch (micro x) <=? cursor x)%nat; [discriminate |].
    set (w := set_cursor x (S (cursor x))) in *.
    assert (Hw : hc_ext x w) by (apply step_hc_ext_same; auto).
    destruct (nth_error (entries I) (cursor x)) as [[c' r |] |]; [| | discriminate].
    + destruct (Nat.eqb c' (sub_cmd (SSample c FInitial))).
      * inversion E; subst y; eapply step_hc_ext_trans; [exact Hw |].
        destruct r as [o | v |]; cbn [on_notify] in *; cbv zeta in *.
        -- apply step_hc_ext_same; auto; destruct Hw as [_ [_ [_ Hc']]]; exact Hc'.
        -- destruct (step_apply_sample_sampled w c v FInitial) as [E1 | (s' & l & cr & l' & E1)];
             rewrite E1 in *.
           ++ destruct (phase (violate w Overflow)) eqn:Pv; [| congruence | congruence].
              rewrite (step_violate_stays _ _ Pv); cbn [after_sample].
              apply step_hc_ext_same; [reflexivity | left; exact Hh | reflexivity |
                                       intros g tk Hin; fields; apply in_or_app; auto].
           ++ fields; unfold w in *; fields; rewrite P in *.
              eexists; cbn; split; [reflexivity |].
              split; [apply step_no_kop_one; intros; discriminate |].
              left; exact Hh.
        -- rewrite (step_violate_stays _ _ Py); apply step_hc_ext_same; auto;
             destruct Hw as [_ [_ [_ Hc']]]; exact Hc'.
      * destruct (c' <? next_cmd x)%nat; inversion E; subst; exact Hw.
    + inversion E; subst y; eapply step_hc_ext_trans; [exact Hw |].
      cbn [on_cancel] in *.
      destruct (step_issue_sample_stays _ _ _ Py) as (_ & _ & _ & _ & _).
      unfold issue_sample in *.
      destruct (step_issue_stays _ _ _ _ _ Py) as (_ & _ & _ & H4 & _).
      destruct (step_issue_trace I (set_held w true) KSample None (fun c => SSample c FInitial))
        as [T | T]; (eexists; split; [exact T |]); fields;
        (split; [apply step_no_kop_one; intros; discriminate | left; rewrite H4; reflexivity]).
Qed.

Lemma step_task_cases : forall t,
  (exists f tok, t = DeliverCancel f tok) \/ (forall f tok, t <> DeliverCancel f tok).
Proof.
  intros t; destruct t; try (right; intros; discriminate); left; eauto.
Qed.

Lemma step_hc_step : forall R I Sch s L, Inv (xs s) -> SInv L (xs s) ->
  NoDup (start_tokens (L ++ fst (step_log R I Sch s))) ->
  phase (xs (step R I Sch s)) = POpen -> hc (xs s) ->
  exists suf, trace (xs (step R I Sch s)) = trace (xs s) ++ suf /\
    (cancelled suf \/ (no_kop suf /\ hc (xs (step R I Sch s)))).
Proof.
  intros R I Sch s L HI SI Hnd Py H.
  assert (P : phase (xs s) = POpen).
  { destruct (phase (xs s)) eqn:E; auto; exfalso; revert Py;
      apply step_closed_step; congruence. }
  destruct (SI P) as [AI HH].
  assert (Hm : forall y, hc_ext (xs s) y ->
     exists suf, trace (set_micro y (S (micro (xs s)))) = trace (xs s) ++ suf /\
       (cancelled suf \/ (no_kop suf /\ hc (set_micro y (S (micro (xs s))))))).
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
      left; exists f, tok; left; reflexivity.
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

(** ** A run *)

Lemma step_hc_run : forall R I Sch j s L, Inv (xs s) -> SInv L (xs s) ->
  NoDup (start_tokens (L ++ fst (elog R I Sch j s))) ->
  phase (xs (iterate R I Sch j s)) = POpen -> hc (xs s) ->
  exists suf, trace (xs (iterate R I Sch j s)) = trace (xs s) ++ suf /\
    (cancelled suf \/ no_kop suf).
Proof.
  intros R I Sch j; induction j as [| j IH]; intros s L HI SI Hnd Py H.
  - exists []; rewrite app_nil_r; split; [reflexivity | right; apply step_no_kop_nil].
  - cbn [iterate] in *; rewrite step_elog_fst, app_assoc in Hnd.
    assert (Ps : phase (xs (step R I Sch s)) = POpen).
    { destruct (phase (xs (step R I Sch s))) eqn:E; auto; exfalso; revert Py;
        apply step_closed_iterate; congruence. }
    assert (Hnd1 : NoDup (start_tokens (L ++ fst (step_log R I Sch s))))
      by (rewrite step_start_tokens_app in Hnd; apply NoDup_app_remove_r in Hnd; exact Hnd).
    destruct (step_hc_step R I Sch s L HI SI Hnd1 Ps H) as [s1 [T1 [C1 | [N1 H1]]]].
    + destruct (step_grows_iterate R I Sch j (step R I Sch s)) as [s2 T2].
      exists (s1 ++ s2); rewrite T2, T1, app_assoc; split; [reflexivity |].
      left; destruct C1 as [f [tok Hin]]; exists f, tok; apply in_or_app; auto.
    + destruct (IH (step R I Sch s) (L ++ fst (step_log R I Sch s))) as [s2 [T2 C2]];
        auto using step_inv_step, step_sinv_step.
      exists (s1 ++ s2); rewrite T2, T1, app_assoc; split; [reflexivity |].
      destruct C2 as [[f [tok Hin]] | N2]; [left; exists f, tok; apply in_or_app; auto |].
      right; apply step_no_kop_app; auto.
Qed.

Lemma step_elog_add : forall R I Sch a b s,
  fst (elog R I Sch (a + b) s) = fst (elog R I Sch a s) ++ fst (elog R I Sch b
                                                                  (iterate R I Sch a s)).
Proof.
  intros R I Sch a; induction a as [| a IH]; intros b s; [reflexivity |].
  replace (S a + b)%nat with (S (a + b)) by lia.
  rewrite !step_elog_fst, IH, app_assoc; reflexivity.
Qed.

Lemma step_iterate_add : forall R I Sch a b s,
  iterate R I Sch (a + b) s = iterate R I Sch b (iterate R I Sch a s).
Proof.
  intros R I Sch a; induction a as [| a IH]; intros b s; [reflexivity |].
  cbn; apply IH.
Qed.

Lemma step_skipn_app : forall {X} (a b : list X), skipn (length a) (a ++ b) = b.
Proof. intros X a; induction a; auto. Qed.

Theorem step_held_cancel_delivered : HeldCancelDelivered.
Proof.
  intros R HM p I Sch n m x y Px Hx Py suffix.
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
  destruct (step_hc_run R I Sch m (iterate R I Sch n s0) (fst (elog R I Sch n s0)))
    as [suf [T C]]; auto.
  - apply step_inv_iterate, step_inv_initial.
  - left; exact Hx.
  - unfold suffix, y; rewrite step_iterate_add, T; fold x; rewrite step_skipn_app.
    destruct C as [C | C]; [left; exact C | right; exact C].
Qed.
