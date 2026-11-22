(** * The await invariant holds of every reachable state.

    Each step of the executor is taken apart into the transitions of [TimeA] and [TimeA2].
    The fact taken from I4, that the trace starts no token twice, is a hypothesis about the
    state a step reaches; a step's intermediate traces are prefixes of it. *)

From Coq Require Import List ZArith Bool Arith Lia Sorting.
From Durable Require Import Runtime Exec Rev3 Statements TimeBase TimeStep TimeL TimeA TimeA2.
Import ListNotations.
Open Scope Z_scope.

(** ** Closing and violations *)

Lemma time_inva_close : forall x c, time_inva x -> time_inva (close x c).
Proof.
  intros x c Hx. destruct (time_close_fields x c) as [T [_ [_ [Op Cl]]]].
  apply (time_inva_frame_quiet x _ [] Hx); [rewrite T, app_nil_r; reflexivity|reflexivity|..].
  - intros t I0. destruct (phase x) eqn:P.
    + rewrite (proj2 (proj2 (proj2 (proj2 (Op eq_refl))))) in I0.
      apply in_app_or in I0 as [I0|I0].
      * right. apply in_map_iff in I0 as [f [<- _]]. reflexivity.
      * apply filter_In in I0 as [I0 _]. left. exact I0.
    + rewrite (proj1 (Cl ltac:(discriminate))) in I0. auto.
    + rewrite (proj1 (Cl ltac:(discriminate))) in I0. auto.
  - destruct (phase x) eqn:P.
    + right. rewrite (proj1 (proj2 (Op eq_refl))). reflexivity.
    + left. apply Cl. discriminate.
    + left. apply Cl. discriminate.
  - intros w E. destruct (phase x) eqn:P.
    + rewrite (proj1 (proj2 (proj2 (Op eq_refl)))) in E. discriminate.
    + destruct (Cl ltac:(discriminate)) as [_ [_ [W [A _]]]]. rewrite W in E. auto.
    + destruct (Cl ltac:(discriminate)) as [_ [_ [W [A _]]]]. rewrite W in E. auto.
  - intros PD. apply Cl; [rewrite PD; discriminate|exact PD].
Qed.

Lemma time_inva_emit : forall x a,
  time_inva x -> time_neutral a && time_quiet a = true -> time_inva (emit x a).
Proof.
  intros x a Hx N. apply (time_inva_frame_quiet x _ [a] Hx); tsimp; auto.
  cbn. rewrite N. reflexivity.
Qed.

Lemma time_inva_violate : forall x v, time_inva x -> time_inva (violate x v).
Proof.
  intros x v Hx. destruct (time_violate_cases x v) as [[-> _]|[_ ->]]; [exact Hx|].
  apply time_inva_close. apply (time_inva_same (emit x (AViolation v)));
    [apply time_inva_emit; auto|reflexivity..].
Qed.

Lemma time_inva_finish : forall x v, time_inva x -> time_inva (finish x v).
Proof.
  intros x v Hx. unfold finish. apply (time_inva_frame_quiet (emit x (AExit v)) _ []);
    [apply time_inva_emit; auto|tsimp; rewrite app_nil_r; reflexivity|reflexivity|..];
    tsimp; auto.
Qed.

Lemma time_inva_set_phase : forall x p,
  time_inva x -> (phase x = PDone -> p = PDone) -> time_inva (set_phase x p).
Proof.
  intros x p Hx H. apply (time_inva_frame_quiet x _ [] Hx); tsimp; auto.
  rewrite app_nil_r. reflexivity.
Qed.

(** ** Events *)

Lemma time_inva_on_release : forall x f tok, time_inva x -> time_inva (on_release x f tok).
Proof.
  intros x f tok Hx.
  assert (Hy : time_inva (match phase x with
                          | POpen => set_queue x (filter (fun t => negb (for_token f tok t))
                                                         (queue x))
                          | _ => x end)).
  { destruct (phase x); [|exact Hx..].
    apply (time_inva_frame_quiet x _ [] Hx); tsimp; auto.
    - rewrite app_nil_r. reflexivity.
    - intros t I0. apply filter_In in I0 as [I0 _]. auto. }
  unfold on_release.
  set (y := match phase x with
            | POpen => set_queue x (filter (fun t => negb (for_token f tok t)) (queue x))
            | _ => x end) in *.
  destruct (phase y) eqn:Py; try exact Hy.
  destruct (awaiter y) as [a|]; [|exact Hy].
  destruct (negb (pair_eqb a (f, tok))); [exact Hy|].
  destruct (waiter y) eqn:Wy.
  - apply (time_inva_frame_quiet y _ [] Hy); tsimp; auto.
    + rewrite app_nil_r. reflexivity.
    + intros w E. discriminate.
  - assert (Hz : time_inva (set_awaiter y None)).
    { apply (time_inva_frame_quiet y _ [] Hy); tsimp; auto.
      - rewrite app_nil_r. reflexivity.
      - intros w E. congruence. }
    destruct (sub y) as [s|] eqn:Sy; [|exact Hz].
    destruct (release_sub s) as [[[f' tok'] s']|] eqn:Rs; [|exact Hz].
    destruct (pair_eqb (f', tok') (f, tok)); [|exact Hz].
    apply (time_inva_frame_quiet y _ [] Hy); tsimp; auto.
    + rewrite app_nil_r. reflexivity.
    + right. destruct s as [| c0 [] |]; cbn in Rs; inversion Rs; reflexivity.
    + intros w E. congruence.
Qed.

(** What a start needs of the state beyond the invariant: the subscription is not the
    initial sample, which [TimeL] gives inside a task. *)
Definition time_noinit (x : XState) : Prop :=
  phase x = POpen -> forall c, sub x <> Some (SSample c FInitial).

Lemma time_split_chain : forall d,
  0 < d -> 1 <= fst (split d) <= max_chunk /\
  time_chain_ok (OSleep (Millis d)) [] (fst (split d)) (snd (split d)).
Proof.
  intros d Hd. unfold split.
  destruct (d <=? max_chunk) eqn:E; cbn [fst snd time_chain_ok time_sum time_rem fold_right].
  - apply Z.leb_le in E. split; [lia|]. split; [left; reflexivity|]. lia.
  - apply Z.leb_gt in E. split; [unfold max_chunk; lia|].
    split; [right; exists (d - max_chunk); split; [reflexivity|unfold max_chunk in *; lia]|].
    lia.
Qed.

(** The chain of an operation issued with no chunk credited yet. *)
Lemma time_issue_chain : forall op,
  time_sleepy op ->
  forall d, op = OSleep d ->
  1 <= fst (match d with Millis m => split m | Forever => (max_chunk, Endless) end) <= max_chunk /\
  time_chain_ok op [] (fst (match d with Millis m => split m | Forever => (max_chunk, Endless) end))
    (snd (match d with Millis m => split m | Forever => (max_chunk, Endless) end)).
Proof.
  intros op Sl d ->. destruct d as [m|].
  - apply time_split_chain. exact Sl.
  - cbn. unfold max_chunk. split; [lia|reflexivity].
Qed.

(** Issuing the command of fiber [f]'s operation, which has no command yet. *)
Lemma time_inva_issue_op : forall I x f tok op mid,
  time_inva x -> waiter x = None ->
  time_after_last (time_is_start f tok) (trace x) = Some (AStart f tok op, mid) ->
  credits f tok mid = [] ->
  time_nodel f tok (queue x) -> ~ In (DeliverCancel f tok) (queue x) ->
  time_inva (issue_op I x f tok op).
Proof.
  intros I x f tok op mid Hx W M C Dl Dc.
  destruct (time_issue_op_cases I x f tok op) as [-> | [k [sb [-> Hsb]]]];
    [apply time_inva_finish; exact Hx|].
  assert (Hs : existsb (time_is_start f tok) (trace x) = true)
    by (eapply time_after_last_existsb; exact M).
  destruct op as [kd a|d]; subst sb.
  - apply time_inva_issue_owned; auto. intros op' mid' M' Sl. rewrite M in M'.
    inversion M'; subst. destruct Sl.
  - apply time_inva_issue_owned; auto. intros op' mid' M' Sl. rewrite M in M'.
    inversion M'; subst. rewrite C.
    destruct (time_issue_chain (OSleep d) Sl d eq_refl) as [K Ch].
    split; [eauto|]. split; [exact K|]. split; [exact Ch|constructor].
Qed.

Lemma time_grows_start_emit : forall I x f tok op,
  phase x <> PDone -> time_grows (emit x (AStart f tok op)) (on_start I x f tok op).
Proof.
  intros I x f tok op Pd. unfold on_start. destruct (phase x); [|apply time_grows_same; reflexivity|contradiction].
  destruct (zero_sleep op); [apply time_grows_same; reflexivity|].
  destruct (awaiter (emit x (AStart f tok op))); [apply time_grows_violate|].
  destruct (held (emit x (AStart f tok op))); [apply time_grows_same; reflexivity|].
  destruct (slot_held (emit x (AStart f tok op))); [apply time_grows_same; reflexivity|].
  eapply time_grows_trans; [|apply time_grows_issue_op]. apply time_grows_same. reflexivity.
Qed.

Lemma time_zero_not_sleepy : forall op, zero_sleep op = true -> ~ time_sleepy op.
Proof.
  intros [k a|[d|]] Z S; cbn in Z, S; try discriminate. apply Z.leb_le in Z. lia.
Qed.

Lemma time_slot_idle : forall x,
  slot_held x = true -> (forall c, sub x <> Some (SSample c FInitial)) ->
  time_idle (sub x) = true.
Proof.
  intros x H N. unfold slot_held in H.
  destruct (sub x) as [[|c []|]|] eqn:E; try discriminate; try reflexivity.
  exfalso. exact (N c eq_refl).
Qed.

Lemma time_inva_on_start : forall I x f tok op,
  time_inva x -> time_noinit x ->
  NoDup (time_stoks (trace (on_start I x f tok op))) ->
  time_inva (on_start I x f tok op).
Proof.
  intros I x f tok op Hx Ni N.
  destruct (phase x) eqn:Pd.
  2: { unfold on_start. rewrite Pd. unfold enqueue.
       assert (Hy : time_inva (emit x (AStart f tok op))).
       { apply time_inva_start; [exact Hx|].
         change (trace x ++ [AStart f tok op]) with (trace (emit x (AStart f tok op))).
         eapply time_nodup_grows; [|exact N].
         apply time_grows_start_emit. rewrite Pd. discriminate. }
       apply (time_inva_frame_quiet _ _ [] Hy); tsimp; auto.
       - rewrite app_nil_r. reflexivity.
       - intros t I0. apply in_app_or in I0 as [I0|[<-|[]]]; auto. }
  2: { unfold on_start. rewrite Pd. exact Hx. }
  assert (N0 : NoDup (time_stoks (trace x ++ [AStart f tok op]))).
  { eapply (time_nodup_grows (emit x (AStart f tok op))); [|exact N].
    apply time_grows_start_emit. rewrite Pd. discriminate. }
  pose proof (time_inva_start x f tok op Hx N0) as Hy.
  assert (Fr : existsb (time_is_start f tok) (trace x) = false) by (eapply time_fresh; exact N0).
  assert (Fd : time_nodel f tok (queue x)).
  { intros o I0. rewrite (ta_r1 x Hx f tok o I0) in Fr. discriminate. }
  assert (Fc : ~ In (DeliverCancel f tok) (queue x)).
  { intros I0. rewrite (ta_r2 x Hx f tok I0) in Fr. discriminate. }
  assert (Fo : existsb (time_is_owned f tok) (trace x ++ [AStart f tok op]) = false).
  { rewrite existsb_app, orb_false_r. destruct (existsb (time_is_owned f tok) (trace x)) eqn:E;
      [|reflexivity]. rewrite (ta_owned x Hx f tok E) in Fr. discriminate. }
  assert (Fm : time_after_last (time_is_start f tok) (trace x ++ [AStart f tok op]) =
               Some (AStart f tok op, [])).
  { rewrite time_after_last_snoc. cbn. rewrite !Nat.eqb_refl. reflexivity. }
  assert (Fs : existsb (time_is_start f tok) (trace x ++ [AStart f tok op]) = true)
    by (eapply time_after_last_existsb; exact Fm).
  assert (Fw : waiter x = None \/ awaiter x <> None).
  { destruct (waiter x) as [[[g t] op']|] eqn:W; [|left; reflexivity]. right.
    rewrite (proj1 (proj2 (proj2 (ta_r3 x Hx g t op' W)))). discriminate. }
  unfold on_start. rewrite Pd.
  destruct (zero_sleep op) eqn:Z.
  { apply time_inva_enq_deliver; tsimp; auto.
    - unfold time_p7_ok. rewrite time_after_last_none by exact Fo. exact Logic.I.
    - destruct (waiter x) as [[[g t] op']|] eqn:W; [|reflexivity].
      destruct (ta_r3 x Hx g t op' W) as [[mid [M _]] _]. cbn.
      destruct (Nat.eqb f g) eqn:E1, (Nat.eqb tok t) eqn:E2; auto.
      apply Nat.eqb_eq in E1, E2. subst. apply time_after_last_existsb in M. congruence.
    - intros op' mid M Sl. rewrite Fm in M. inversion M; subst.
      exfalso. exact (time_zero_not_sleepy op' Z Sl). }
  destruct (awaiter (emit x (AStart f tok op))) eqn:Ay; [apply time_inva_violate; exact Hy|].
  assert (W0 : waiter (emit x (AStart f tok op)) = None) by (tsimp; destruct Fw; [assumption|contradiction]).
  assert (Hz : time_inva (set_awaiter (emit x (AStart f tok op)) (Some (f, tok)))).
  { apply (time_inva_frame_quiet (emit x (AStart f tok op)) _ [] Hy); tsimp; auto.
    - rewrite app_nil_r. reflexivity.
    - intros w E. congruence. }
  destruct (held (emit x (AStart f tok op))).
  { assert (Hz' : time_inva (set_held (set_awaiter (emit x (AStart f tok op)) (Some (f, tok))) false))
      by (apply (time_inva_same _ _ Hz); reflexivity).
    apply time_inva_enq_cancel; tsimp; auto.
    - unfold time_p8a_ok. rewrite time_after_last_none by exact Fo. exact Logic.I.
    - unfold time_p8b_ok. rewrite Fm. intros _. reflexivity.
    - rewrite W0. reflexivity. }
  destruct (slot_held (emit x (AStart f tok op))) eqn:Sh.
  { apply time_inva_set_waiter; tsimp; auto. split; [|split; [|split; [|split; [|split]]]].
    - exists []. split; [exact Fm|reflexivity].
    - exact Fo.
    - reflexivity.
    - apply time_slot_idle; [exact Sh|]. tsimp. apply Ni. exact Pd.
    - exact Fd.
    - exact Fc. }
  apply (time_inva_issue_op I _ f tok op []); tsimp; auto.
Qed.

Lemma time_inva_on_event : forall I x e,
  time_inva x -> time_noinit x -> NoDup (time_stoks (trace (on_event I x e))) ->
  time_inva (on_event I x e).
Proof.
  intros I x e Hx Ni N. unfold on_event in *.
  destruct (phase x); try exact Hx;
  (destruct e as [f tok op|f tok|pr t|f|r];
   [apply time_inva_on_start; assumption
   |apply time_inva_on_release; exact Hx
   |destruct (Nat.eqb pr 0);
      [unfold enqueue; apply (time_inva_frame_quiet x _ [] Hx); tsimp; auto;
       [rewrite app_nil_r; reflexivity
       |intros t' I0; apply in_app_or in I0 as [I0|[<-|[]]]; auto]
      |apply time_inva_violate; exact Hx]
   |apply (time_inva_same _ _ Hx); reflexivity
   |destruct (root_exit x);
      [apply time_inva_violate; exact Hx
      |apply time_inva_close; apply (time_inva_same _ _ Hx); reflexivity]]).
Qed.

Lemma time_inva_clock : forall x f,
  time_inva x ->
  time_inva (match phase x with PDone => x | _ => emit x (AClock f (logical x)) end).
Proof. intros x f Hx. destruct (phase x); try exact Hx; apply time_inva_emit; auto. Qed.

Lemma time_inva_draw : forall I x f,
  time_inva x ->
  time_inva (match phase x with
             | PDone => x
             | _ => emit (set_draws x (S (draws x))) (ADraw f (stream I (draws x)))
             end).
Proof.
  intros I x f Hx. destruct (phase x); try exact Hx;
    (apply time_inva_emit; [apply (time_inva_same _ _ Hx); reflexivity|reflexivity]).
Qed.

Lemma time_inva_reg : forall x f, time_inva x -> time_inva (time_reg x f).
Proof.
  intros x f Hx. unfold time_reg.
  assert (H1 : time_inva (match phase x with PDone => x | _ => emit x (ARegister f) end))
    by (destruct (phase x); try exact Hx; apply time_inva_emit; auto).
  apply (time_inva_same _ _ H1); reflexivity.
Qed.

Lemma time_inva_interp : forall I X (s : Script X) x,
  time_inva x -> time_ctxl x -> NoDup (time_stoks (trace (fst (interp I x s)))) ->
  time_inva (fst (interp I x s)).
Proof.
  intros I X s x Hx Hc N.
  enough (G : time_inva (fst (interp I x s)) /\ time_ctxl (fst (interp I x s)))
    by exact (proj1 G).
  revert x Hx Hc N.
  refine (fun x Hx Hc N => time_interp_ind_nodup
    (fun y => time_inva y /\ time_ctxl y) I _ _ _ _ X s x (conj Hx Hc) N).
  - intros y e [Hy Cy] Ny. split; [|apply time_ctxl_on_event; exact Cy].
    apply time_inva_on_event; [exact Hy| |exact Ny].
    intros Ho. apply time_ctxl_not_initial; assumption.
  - intros y f [Hy Cy]. split; [apply time_inva_clock|apply time_ctxl_clock]; assumption.
  - intros y f [Hy Cy]. split; [apply time_inva_draw|apply time_ctxl_draw]; assumption.
  - intros y f [Hy Cy]. split; [apply time_inva_reg; exact Hy|apply time_ctxl_reg; exact Cy].
Qed.

(** ** Running a task *)

Lemma time_claim_deliver : forall x f tok o,
  time_inva x -> phase x <> PDone -> In (Deliver f tok o) (queue x) ->
  time_claim_at (trace x) (ADelivered f tok o).
Proof.
  intros x f tok o Hx Pd I0. split; [|exact (ta_p7 x Hx f tok o I0)].
  pose proof (ta_ld x Hx f tok) as L. unfold time_ldinv, time_p3_ok in *.
  destruct (time_after_last (time_is_start f tok) (trace x)) as [[b mid]|] eqn:E;
    [|exact Logic.I].
  destruct b; try exact Logic.I.
  destruct (time_after_last_start_some _ _ _ _ _ E) as [op1 Eo]. inversion Eo; subst.
  assert (Gen : time_sleepy op1 -> time_total_ok op1 (credits f tok mid) /\
                time_bounds (credits f tok mid)).
  { intros Sl. destruct (L Sl) as [B St]. split; [|exact B].
    destruct St as [PD|[[S1 _]|[S2|[S3|[[T _]|[Dl _]]]]]].
    - contradiction.
    - exfalso. exact (time_r3_nodel x Hx f tok op1 S1 o I0).
    - destruct S2 as [c [d [k [rest [_ [_ [_ Nd]]]]]]]. exfalso. exact (Nd o I0).
    - destruct S3 as [c [k [rest [_ [_ [_ Nd]]]]]]. exfalso. exact (Nd o I0).
    - exact T.
    - exfalso. exact (Dl o I0). }
  destruct op1 as [k a|[d|]]; cbn; [exact Logic.I| |].
  - intros Hd. exact (Gen Hd).
  - destruct (Gen Logic.I) as [T _]. exact T.
Qed.

Lemma time_pair_eqb_true : forall a f tok, pair_eqb a (f, tok) = true -> a = (f, tok).
Proof.
  intros [g t] f tok H. unfold pair_eqb in H. cbn in H. apply time_eqb_pair in H as [-> ->].
  reflexivity.
Qed.

Lemma time_inva_run_head : forall R I x r t rest,
  time_inva x -> time_invl x -> phase x <> PDone -> queue x = t :: rest ->
  NoDup (time_stoks (trace (fst (run_head R I x r t rest)))) ->
  time_inva (fst (run_head R I x r t rest)).
Proof.
  intros R I x r t rest Hx Hl Pd Q N.
  assert (Hc : time_ctxl x).
  { split; [exact Hl|]. intros Ho He. destruct (tl_empty x Hl Ho He) as [E _].
    rewrite Q in E. discriminate. }
  unfold run_head in *.
  set (x0 := set_progress (set_queue x rest) (S (progress x))) in *.
  assert (H0 : time_ctxl x0) by (apply (time_ctxl_fields _ _ Hc); reflexivity).
  assert (A0 : time_inva x0).
  { apply (time_inva_frame_quiet x _ [] Hx); subst x0; tsimp; auto.
    - rewrite app_nil_r. reflexivity.
    - intros t' I0. left. rewrite Q. right. exact I0. }
  assert (Ht : In t (queue x)) by (rewrite Q; left; reflexivity).
  set (x1 := match task_action t with Some a => emit x0 a | None => x0 end) in *.
  assert (H1 : time_ctxl x1) by (subst x1; destruct t; cbn; try exact H0;
    apply time_ctxl_emit; auto).
  assert (A1 : time_inva x1).
  { subst x1. destruct t as [|q|f tok o|f tok|f tok|f]; cbn [task_action]; try exact A0.
    - apply (time_inva_frame x0 _ [ADelivered f tok o] A0); subst x0; tsimp; auto.
      + apply time_claims_snoc; [exact (ta_claims x Hx)|].
        apply time_claim_deliver; assumption.
    - apply (time_inva_frame x0 _ [ACancelled f tok] A0); subst x0; tsimp; auto.
      + apply time_claims_snoc; [exact (ta_claims x Hx)|]. exact (ta_p8 x Hx f tok Ht).
    - apply time_inva_emit; auto. }
  set (x2 := match t, awaiter x1 with
             | Deliver f tok _, Some a | DeliverCancel f tok, Some a =>
                 if pair_eqb a (f, tok) then set_awaiter x1 None else x1
             | _, _ => x1
             end).
  assert (Wx1 : waiter x1 = waiter x) by (subst x1 x0; destruct t; reflexivity).
  assert (Ax1 : awaiter x1 = awaiter x) by (subst x1 x0; destruct t; reflexivity).
  assert (H2 : time_ctxl x2).
  { subst x2. destruct t; try exact H1; destruct (awaiter x1) as [a|]; try exact H1;
      destruct (pair_eqb a _); try exact H1; apply (time_ctxl_fields _ _ H1); reflexivity. }
  assert (A2 : time_inva x2).
  { subst x2. destruct t as [|q|f tok o|f tok|f tok|f]; try exact A1;
      destruct (awaiter x1) as [a|] eqn:Ea; try exact A1;
      destruct (pair_eqb a (f, tok)) eqn:Pe; try exact A1;
      apply time_pair_eqb_true in Pe; subst a.
  all: apply (time_inva_frame_quiet x1 _ [] A1); tsimp; auto;
    try (rewrite app_nil_r; reflexivity).
  all: intros [[g t'] op'] E; exfalso; rewrite Wx1 in E;
        destruct (ta_r3 x Hx g t' op' E) as [_ [_ [Aw [_ [Dl Dc]]]]].
  all: assert (Ae : awaiter x = Some (f, tok)) by (rewrite <- Ax1; reflexivity);
    rewrite Aw in Ae; inversion Ae; subst; first [exact (Dl o Ht) | exact (Dc Ht)]. }
  fold x2. apply time_inva_interp; [exact A2|exact H2|exact N].
Qed.

(** ** Turn boundaries *)

Lemma time_after_last_snoc_false : forall p t a,
  p a = false ->
  time_after_last p (t ++ [a]) =
  match time_after_last p t with Some (b, s) => Some (b, s ++ [a]) | None => None end.
Proof. intros p t a H. rewrite time_after_last_snoc, H. reflexivity. Qed.

(** An await whose subscription is retired or replaced: nothing can be delivered for it. *)
Lemma time_ldinv_dead : forall f tok x x' new,
  time_ldinv f tok x -> trace x' = trace x ++ new -> forallb time_neutral new = true ->
  time_nodel f tok (queue x') -> time_sub_live f tok (sub x') = false ->
  time_waiter_is f tok (waiter x') = false -> time_ldinv f tok x'.
Proof.
  intros f tok x x' new L T N Dl Lv W. unfold time_ldinv in *. rewrite T.
  rewrite time_after_last_ext by (apply time_neutral_start; exact N).
  destruct (time_after_last (time_is_start f tok) (trace x)) as [[b mid]|]; [|exact Logic.I].
  destruct b; try exact Logic.I. intros Sl. destruct (L Sl) as [B _]. split.
  - rewrite time_credits_app, (time_neutral_credits f tok new N), app_nil_r. exact B.
  - right; right; right; right; right. auto.
Qed.

Lemma time_link_chain : forall op cr k rest ch rest',
  time_chain_ok op cr k rest -> 1 <= k <= max_chunk -> time_bounds cr ->
  link_of rest = Some (ch, rest') ->
  1 <= ch <= max_chunk /\ time_chain_ok op (cr ++ [k]) ch rest' /\ time_bounds (cr ++ [k]).
Proof.
  intros op cr k rest ch rest' Ch K B L.
  assert (Bk : time_bounds (cr ++ [k])) by (apply Forall_app; split; [exact B|repeat constructor; lia]).
  destruct op as [? ?|[d|]]; cbn in Ch; [contradiction| |].
  - destruct Ch as [[->|[r [-> R]]] Sm]; [discriminate|]. cbn in L.
    unfold split in L. destruct (r <=? max_chunk) eqn:E; inversion L; subst.
    + apply Z.leb_le in E. split; [lia|]. split; [|exact Bk]. cbn.
      split; [left; reflexivity|]. rewrite time_sum_app. cbn. lia.
    + apply Z.leb_gt in E. split; [unfold max_chunk; lia|]. split; [|exact Bk]. cbn.
      split; [right; exists (r - max_chunk); split; [reflexivity|unfold max_chunk in *; lia]|].
      rewrite time_sum_app. cbn. lia.
  - subst rest. cbn in L. inversion L; subst. split; [unfold max_chunk; lia|].
    split; [reflexivity|exact Bk].
Qed.

Lemma time_link_total : forall op cr k rest,
  time_chain_ok op cr k rest -> link_of rest = None -> time_total_ok op (cr ++ [k]).
Proof.
  intros op cr k rest Ch L. destruct op as [? ?|[d|]]; cbn in Ch |- *; [contradiction| |].
  - destruct Ch as [[->|[r [-> _]]] Sm]; [|discriminate]. rewrite time_sum_app. cbn in Sm |- *.
    lia.
  - subst rest. discriminate.
Qed.

Lemma time_credits_sampled : forall f tok mid c v l k,
  0 < k ->
  credits f tok (mid ++ [ASampled c v l (Some (f, tok, k))]) = credits f tok mid ++ [k].
Proof.
  intros. rewrite time_credits_app. unfold credits at 2. cbn. rewrite !Nat.eqb_refl.
  reflexivity.
Qed.

Lemma time_refs_unique : forall f tok g t s,
  time_sub_refs f tok s = true -> time_sub_refs g t s = true -> g = f /\ t = tok.
Proof.
  intros f tok g t [[c f' tok' op k rest|c [|f' tok' o|f' tok' k rest|f' tok'|f' tok' k]|c]|]
    H1 H2; cbn in H1, H2; try discriminate;
  apply time_eqb_pair in H1 as [-> ->]; apply time_eqb_pair in H2 as [-> ->]; auto.
Qed.

Lemma time_issue_sample_cases : forall I x after,
  issue_sample I x after = finish x VMismatch \/
  issue_sample I x after =
    set_sub (set_next_cmd (emit x (ACommand (next_cmd x) KSample None)) (S (next_cmd x)))
      (Some (SSample (next_cmd x) after)).
Proof. intros. unfold issue_sample. apply time_issue_cases. Qed.

(** A sample command for an await whose subscription it replaces. *)
Lemma time_inva_resample : forall I x f tok after,
  time_inva x -> waiter x = None -> time_sub_refs f tok (sub x) = true ->
  (forall g t, time_sub_refs g t (Some (SSample 0 after)) = true -> g = f /\ t = tok) ->
  (forall c, time_ldinv f tok
     (set_sub (set_next_cmd (emit x (ACommand (next_cmd x) KSample None)) (S (next_cmd x)))
        (Some (SSample c after)))) ->
  time_inva (issue_sample I x after).
Proof.
  intros I x f tok after Hx W R Ra L.
  destruct (time_issue_sample_cases I x after) as [-> | ->]; [apply time_inva_finish; exact Hx|].
  apply time_inva_issue_sample; [exact Hx|exact W| |].
  - intros g t Rg. assert (Rg0 : time_sub_refs g t (Some (SSample 0 after)) = true)
      by (destruct after; exact Rg).
    destruct (Ra g t Rg0) as [-> ->]. exact R.
  - intros g t Rg. destruct (time_refs_unique f tok g t _ R Rg) as [-> ->]. apply L.
Qed.

Lemma time_ld_of_sub : forall x f tok,
  time_inva x -> time_sub_refs f tok (sub x) = true ->
  exists op mid, time_after_last (time_is_start f tok) (trace x) = Some (AStart f tok op, mid)
    /\ (time_sleepy op -> time_ld f tok op mid x).
Proof.
  intros x f tok Hx R. destruct (ta_r4 x Hx f tok R) as [[op [mid [M _]]] _].
  exists op, mid. split; [exact M|]. pose proof (ta_ld x Hx f tok) as L.
  unfold time_ldinv in L. rewrite M in L. exact L.
Qed.

Lemma time_waiter_none : forall x,
  time_inva x -> time_idle (sub x) = false -> waiter x = None.
Proof.
  intros x Hx I0. destruct (waiter x) as [w|] eqn:W; [|reflexivity].
  rewrite (time_r3_idle x Hx w W) in I0. discriminate.
Qed.

Lemma time_resample_ldinv_dead : forall x f tok c,
  time_inva x -> waiter x = None -> time_nodel f tok (queue x) ->
  time_ldinv f tok
    (set_sub (set_next_cmd (emit x (ACommand (next_cmd x) KSample None)) (S (next_cmd x)))
       (Some (SSample c (FCancelled f tok)))).
Proof.
  intros x f tok c Hx W Dl.
  apply (time_ldinv_dead f tok x _ [ACommand (next_cmd x) KSample None] (ta_ld x Hx f tok));
    tsimp; auto. rewrite W. reflexivity.
Qed.

(** The cancel signal through the subscription, at a turn boundary. *)
Lemma time_inva_cancel : forall I x s,
  time_inva x -> time_invl x -> phase x = POpen -> sub x = Some s -> queue x = [] ->
  time_inva (on_cancel I x s).
Proof.
  intros I x s Hx Hl Ph S Q.
  assert (Dl : forall f tok, time_nodel f tok (queue x)) by (intros f tok o; rewrite Q; auto).
  destruct s as [c0 f tok op k rest|c0 [|f tok o|f tok k rest|f tok|f tok k]|c0];
    cbn [on_cancel].
  - assert (W : waiter x = None) by (apply time_waiter_none; [exact Hx|rewrite S; reflexivity]).
    apply (time_inva_resample I x f tok); auto.
    + rewrite S. cbn. rewrite !Nat.eqb_refl. reflexivity.
    + intros g t R. cbn in R. apply time_eqb_pair in R. exact R.
    + intros c. apply time_resample_ldinv_dead; auto.
  - assert (Ae : applied (trace x) = []) by (apply (tl_init x Hl Ph); exists c0; exact S).
    destruct (tl_empty x Hl Ph Ae) as [_ [W _]].
    assert (Hy : time_inva (set_held x true)) by (apply (time_inva_same _ _ Hx); reflexivity).
    destruct (time_issue_sample_cases I (set_held x true) FInitial) as [-> | ->];
      [apply time_inva_finish; exact Hy|].
    apply time_inva_issue_sample; tsimp; auto; [intros g t R; discriminate|].
    intros g t R. rewrite S in R. discriminate.
  - assert (W : waiter x = None) by (apply time_waiter_none; [exact Hx|rewrite S; reflexivity]).
    apply (time_inva_resample I x f tok); auto.
    + rewrite S. cbn. rewrite !Nat.eqb_refl. reflexivity.
    + intros g t R. cbn in R. apply time_eqb_pair in R. exact R.
    + intros c. apply time_resample_ldinv_dead; auto.
  - assert (W : waiter x = None) by (apply time_waiter_none; [exact Hx|rewrite S; reflexivity]).
    apply (time_inva_resample I x f tok); auto.
    + rewrite S. cbn. rewrite !Nat.eqb_refl. reflexivity.
    + intros g t R. cbn in R. apply time_eqb_pair in R. exact R.
    + intros c. apply time_resample_ldinv_dead; auto.
  - assert (W : waiter x = None) by (apply time_waiter_none; [exact Hx|rewrite S; reflexivity]).
    apply (time_inva_resample I x f tok); auto.
    + rewrite S. cbn. rewrite !Nat.eqb_refl. reflexivity.
    + intros g t R. cbn in R. apply time_eqb_pair in R. exact R.
    + intros c. apply time_resample_ldinv_dead; auto.
  - apply (time_inva_frame_quiet x _ [] Hx); tsimp; auto. rewrite app_nil_r. reflexivity.
  - apply (time_inva_frame_quiet x _ [] Hx); tsimp; auto. rewrite app_nil_r. reflexivity.
Qed.

(** An applied sample and what follows it. *)
Lemma time_inva_apply : forall I x c v after,
  time_inva x -> time_invl x -> phase x = POpen -> sub x = Some (SSample c after) ->
  queue x = [] -> (forall f tok k, after <> FReleased f tok k) ->
  time_inva (let x1 := apply_sample x c v after in
             match phase x1 with POpen => after_sample I x1 after | _ => x1 end).
Proof.
  intros I x c v after Hx Hl Ph S Q Nr. cbv zeta.
  assert (W : waiter x = None).
  { destruct after; try (apply time_waiter_none; [exact Hx|rewrite S; reflexivity]).
    exfalso. eapply Nr. reflexivity. }
  unfold apply_sample.
  set (l := match after with
            | FInitial => v
            | _ => Z.max (logical x + match time_credit after with
                                      | Some (_, _, k) => k | None => 0 end) v
            end).
  change (match after with
          | FLink f tok k _ => if 0 <? k then Some (f, tok, k) else None
          | _ => None end) with (time_credit after).
  fold l.
  destruct (max_safe <? l).
  { pose proof (time_violate_fields x Overflow (tl_viol x Hl)) as [_ [_ [Pv _]]].
    destruct (phase (violate x Overflow)); try contradiction;
      apply time_inva_violate; exact Hx. }
  set (x1 := set_sub (set_logical (emit x (ASampled c v l (time_credit after))) l) None).
  assert (A1 : time_inva x1) by (apply time_inva_applied; auto; rewrite Ph; discriminate).
  assert (P1 : phase x1 = POpen) by (subst x1; tsimp; exact Ph).
  rewrite P1.
  assert (T1 : trace x1 = trace x ++ [ASampled c v l (time_credit after)]) by reflexivity.
  assert (Ext : forall p, p (ASampled c v l (time_credit after)) = false ->
     time_after_last p (trace x1) =
     match time_after_last p (trace x) with
     | Some (b, s) => Some (b, s ++ [ASampled c v l (time_credit after)])
     | None => None end)
    by (intros p Hp; rewrite T1; apply time_after_last_snoc_false; exact Hp).
  destruct after as [|f tok o|f tok k rest|f tok|f tok k]; cbn [after_sample].
  - apply (time_inva_frame_quiet x1 _ [] A1); unfold enqueue; tsimp; auto.
    + rewrite app_nil_r. reflexivity.
    + intros t I0. apply in_app_or in I0 as [I0|[<-|[]]]; auto.
  - assert (R : time_sub_refs f tok (sub x) = true)
      by (rewrite S; cbn; rewrite !Nat.eqb_refl; reflexivity).
    destruct (time_ld_of_sub x f tok Hx R) as [op [mid [M L]]].
    apply time_inva_enq_deliver; auto.
    + rewrite T1. apply time_existsb_app_true. eapply time_after_last_existsb. exact M.
    + unfold time_p7_ok. rewrite Ext by reflexivity.
      destruct (time_after_last (time_is_owned f tok) (trace x)) as [[b s]|]; [|exact Logic.I].
      rewrite existsb_app. cbn. apply orb_true_r.
    + subst x1. tsimp. rewrite W. reflexivity.
    + intros op' mid' M' Sl. rewrite Ext, M in M' by reflexivity. inversion M'; subst.
      exfalso. eapply (time_ld_fresult f tok op' mid x c o (L Sl) S W). rewrite Ph. discriminate.
  - assert (R : time_sub_refs f tok (sub x) = true)
      by (rewrite S; cbn; rewrite !Nat.eqb_refl; reflexivity).
    destruct (time_ld_of_sub x f tok Hx R) as [op [mid [M L]]].
    assert (Pd : phase x <> PDone) by (rewrite Ph; discriminate).
    assert (M1 : time_after_last (time_is_start f tok) (trace x1) =
                 Some (AStart f tok op, mid ++ [ASampled c v l (time_credit (FLink f tok k rest))]))
      by (rewrite Ext, M by reflexivity; reflexivity).
    assert (Cr : time_sleepy op -> credits f tok
               (mid ++ [ASampled c v l (time_credit (FLink f tok k rest))]) =
               credits f tok mid ++ [k]).
    { intros Sl. destruct (time_ld_flink f tok op mid x c k rest (L Sl) S W Pd) as [K _].
      unfold time_credit. destruct (0 <? k) eqn:E; [|apply Z.ltb_ge in E; lia].
      apply time_credits_sampled. lia. }
    assert (Hs : existsb (time_is_start f tok) (trace x1) = true)
      by (eapply time_after_last_existsb; exact M1).
    destruct (link_of rest) as [[ch rest']|] eqn:Lk.
    + destruct (time_issue_cases I x1 (KOp (OSleep (Millis ch))) (Some (f, tok))
        (fun c0 => SOp c0 f tok (OSleep (Millis ch)) ch rest')) as [-> | ->];
        [apply time_inva_finish; exact A1|].
      apply time_inva_issue_owned; auto.
      1: subst x1; tsimp; intros ? I0; rewrite Q in I0; destruct I0.
      1: subst x1; tsimp; intros I0; rewrite Q in I0; destruct I0.
      intros op' mid' M' Sl. rewrite M1 in M'. injection M' as <- <-.
        unfold time_credit in Cr. rewrite (Cr Sl).
        destruct (time_ld_flink f tok op mid x c k rest (L Sl) S W Pd) as [K [Ch B]].
        destruct (time_link_chain op _ k rest ch rest' Ch K B Lk) as [K' [Ch' B']].
        split; [eauto|]. auto.
    + apply time_inva_enq_deliver; auto.
      * unfold time_p7_ok. rewrite Ext by reflexivity.
        destruct (time_after_last (time_is_owned f tok) (trace x)) as [[b s]|];
          [|exact Logic.I].
        rewrite existsb_app. cbn. apply orb_true_r.
      * subst x1. tsimp. rewrite W. reflexivity.
      * intros op' mid' M' Sl. rewrite M1 in M'. injection M' as <- <-.
        unfold time_credit in Cr. rewrite (Cr Sl). split; [|reflexivity].
        destruct (time_ld_flink f tok op mid x c k rest (L Sl) S W Pd) as [K [Ch B]].
        eapply time_link_total; eassumption.
  - assert (R : time_sub_refs f tok (sub x) = true)
      by (rewrite S; cbn; rewrite !Nat.eqb_refl; reflexivity).
    destruct (ta_r4 x Hx f tok R) as [[op [mid [M Mo]]] Sc].
    apply time_inva_enq_cancel; auto.
    + rewrite T1. apply time_existsb_app_true. eapply time_after_last_existsb. exact M.
    + unfold time_p8a_ok. unfold time_since_credits in Sc. rewrite Ext by reflexivity.
      destruct (time_after_last (time_is_owned f tok) (trace x)) as [[b s]|]; [|exact Logic.I].
      split; [rewrite existsb_app; cbn; apply orb_true_r|].
      rewrite time_credits_app, Sc. reflexivity.
    + unfold time_p8b_ok. rewrite Ext, M by reflexivity. intros Hc. exfalso.
      rewrite existsb_app in Hc. apply orb_false_iff in Hc as [Hc _].
      assert (existsb time_is_cmd mid = true).
      { apply existsb_exists in Mo as [a [Ia Oa]]. apply existsb_exists. exists a.
        split; [exact Ia|]. destruct a; try discriminate. reflexivity. }
      congruence.
    + subst x1. tsimp. rewrite W. reflexivity.
  - exfalso. eapply Nr. reflexivity.
Qed.

Lemma time_inva_set_sub_idle : forall x s,
  time_inva x -> time_idle (Some s) = true \/ s = s -> time_idle (Some s) = true ->
  time_inva (set_sub x (Some s)).
Proof.
  intros x s Hx _ I0. apply (time_inva_frame_quiet x _ [] Hx); tsimp; auto.
  rewrite app_nil_r. reflexivity.
Qed.

Lemma time_inva_set_sub_none : forall x, time_inva x -> time_inva (set_sub x None).
Proof.
  intros x Hx. apply (time_inva_frame_quiet x _ [] Hx); tsimp; auto.
  rewrite app_nil_r. reflexivity.
Qed.

(** The subscription's notification, at a turn boundary. *)
Lemma time_inva_notify : forall I x s r,
  time_inva x -> time_invl x -> phase x = POpen -> sub x = Some s -> queue x = [] ->
  time_inva (on_notify I x s r).
Proof.
  intros I x s r Hx Hl Ph S Q.
  assert (Pd : phase x <> PDone) by (rewrite Ph; discriminate).
  destruct s as [c0 f tok op k rest|c0 after|c0].
  - assert (W : waiter x = None) by (apply time_waiter_none; [exact Hx|rewrite S; reflexivity]).
    assert (R : time_sub_refs f tok (sub x) = true)
      by (rewrite S; cbn; rewrite !Nat.eqb_refl; reflexivity).
    destruct r as [o|v|]; destruct op as [ka aa|d]; cbn [on_notify]; try exact Hx.
    + apply (time_inva_resample I x f tok); auto.
      * intros g t Rg. cbn in Rg. apply time_eqb_pair in Rg. exact Rg.
      * intros c. destruct (time_ld_of_sub x f tok Hx R) as [op [mid [M L]]].
        unfold time_ldinv. tsimp. rewrite time_after_last_snoc_false, M by reflexivity.
        intros Sl. exfalso.
        destruct (time_ld_sop f tok op mid x c0 _ k rest (L Sl) S W Pd) as [[d' E] _].
        discriminate.
    + apply (time_inva_resample I x f tok); auto.
      * intros g t Rg. cbn in Rg. apply time_eqb_pair in Rg. exact Rg.
      * intros c. destruct (time_ld_of_sub x f tok Hx R) as [op [mid [M L]]].
        unfold time_ldinv. tsimp. rewrite time_after_last_snoc_false, M by reflexivity.
        intros Sl. destruct (L Sl) as [B _].
        destruct (time_ld_sop f tok op mid x c0 _ k rest (L Sl) S W Pd) as [_ [K [Ch Dl]]].
        assert (Cr : credits f tok (mid ++ [ACommand (next_cmd x) KSample None]) =
                     credits f tok mid) by (rewrite time_credits_app; cbn; apply app_nil_r).
        unfold time_ld. rewrite Cr. split; [exact B|]. right; right; right; left. tsimp.
        exists c, k, rest. auto.
  - destruct after as [|f tok o|f tok k rest|f tok|f tok k];
      [destruct r as [o'|v|]; cbn [on_notify]..|cbn [on_notify]; apply time_inva_set_sub_none; exact Hx].
    all: try exact Hx.
    all: try (apply time_inva_violate; exact Hx).
    all: apply (time_inva_apply I x); auto; intros; discriminate.
  - cbn [on_notify]. destruct r; apply time_inva_set_sub_none; exact Hx.
Qed.

Lemma time_inva_issue_waiter : forall I x f tok op,
  time_inva x -> waiter x = Some (f, tok, op) ->
  time_inva (issue_op I (set_waiter x None) f tok op).
Proof.
  intros I x f tok op Hx Hw.
  destruct (ta_r3 x Hx f tok op Hw) as [[mid [M Ms]] [O [_ [_ [Dl Dc]]]]].
  assert (Hz : time_inva (set_waiter x None)).
  { apply (time_inva_frame_quiet x _ [] Hx); tsimp; auto;
      [rewrite app_nil_r; reflexivity|intros w Ew; discriminate]. }
  apply (time_inva_issue_op I _ f tok op mid Hz); tsimp; auto.
  apply time_credits_nil_samples. exact Ms.
Qed.

Lemma time_inva_boundary : forall I Sch x x',
  time_inva x -> time_invl x -> queue x = [] -> at_boundary I Sch x = Some x' ->
  time_inva x'.
Proof.
  intros I Sch x x' Hx Hl Q E. unfold at_boundary in E.
  destruct (phase x) eqn:Ph; try discriminate.
  2: { inversion E; subst. apply time_inva_finish. exact Hx. }
  destruct (held x) eqn:Hh, (waiter x) as [[[f tok] op]|] eqn:Hw.
  1: { inversion E; subst.
       destruct (ta_r3 x Hx f tok op Hw) as [[mid [M Ms]] [O [_ [_ [Dl Dc]]]]].
       assert (Hz : time_inva (set_waiter (set_held x false) None)).
       { apply (time_inva_frame_quiet x _ [] Hx); tsimp; auto;
           [rewrite app_nil_r; reflexivity|intros w Ew; discriminate]. }
       apply time_inva_enq_cancel; tsimp; auto.
       - eapply time_after_last_existsb. exact M.
       - unfold time_p8a_ok. rewrite time_after_last_none by exact O. exact Logic.I.
       - unfold time_p8b_ok. rewrite M. intros _. exact Ms. }
  all: destruct (sub x) as [s|] eqn:Hs;
    [|inversion E; subst; first [apply time_inva_violate; exact Hx
                                |apply time_inva_issue_waiter; assumption]].
  all: unfold at_boundary_sub in E;
    destruct (arrived Sch (micro x) <=? cursor x)%nat; [discriminate|];
    destruct (nth_error (entries I) (cursor x)) as [[c r|]|]; try discriminate;
    [destruct (Nat.eqb c (sub_cmd s));
      [|destruct (c <? next_cmd x)%nat; inversion E; subst;
        apply (time_inva_same _ _ Hx); reflexivity]
    |].
  all: inversion E; subst; clear E.
  all: assert (Hc : time_inva (set_cursor x (S (cursor x)))) by
    (apply (time_inva_same _ _ Hx); reflexivity).
  all: assert (Hcl : time_invl (set_cursor x (S (cursor x)))) by
    (apply (time_invl_fields _ _ Hl); reflexivity).
  all: first [apply time_inva_notify | apply time_inva_cancel]; tsimp; assumption.
Qed.

Lemma time_inva_step : forall R I Sch s,
  time_inva (xs s) -> time_invl (xs s) ->
  NoDup (time_stoks (trace (xs (step R I Sch s)))) ->
  time_inva (xs (step R I Sch s)).
Proof.
  intros R I Sch s Hx Hl N. unfold step in *. cbv zeta in *.
  assert (Mi : forall y m, time_inva y -> time_inva (set_micro y m))
    by (intros y m Hy; apply (time_inva_same _ _ Hy); reflexivity).
  destruct (phase (xs s)) eqn:Ph; try exact Hx.
  all: destruct (stop_due Sch (xs s));
    [tsimp; apply Mi; apply time_inva_set_phase; auto|].
  all: destruct (foreign_due I (xs s)) as [fi|];
    [tsimp; apply Mi; assert (Hf : time_inva (set_fseen (xs s) (Some (progress (xs s)))))
       by (apply (time_inva_same _ _ Hx); reflexivity);
     destruct fi; cbn [on_foreign]; try apply time_inva_violate; exact Hf|].
  all: destruct (cut_due Sch (xs s)) as [k|];
    [tsimp; apply Mi; unfold on_cut;
     assert (He : time_inva (emit (xs s) (ACut k))) by (apply time_inva_emit; auto);
     destruct k; [apply time_inva_close; exact He|apply time_inva_close; exact He|
                  apply time_inva_set_phase; auto]|].
  all: destruct (queue (xs s)) as [|t rest] eqn:Q.
  1,3: destruct (at_boundary I Sch (xs s)) as [x'|] eqn:B; tsimp; apply Mi;
    [apply (time_inva_same x'); try reflexivity; eapply time_inva_boundary; eauto|exact Hx].
  all: destruct (run_head R I (xs s) (rs s) t rest) as [x' r'] eqn:E; tsimp; apply Mi.
  all: replace x' with (fst (run_head R I (xs s) (rs s) t rest)) in * by (rewrite E; reflexivity).
  all: apply time_inva_run_head; auto; rewrite Ph; discriminate.
Qed.
