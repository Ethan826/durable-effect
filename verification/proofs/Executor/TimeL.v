(** * The invariant behind P2, P4, P5 and P6: how [L] moves.

    [L] changes only when a sample is applied. The first sample applied is the initial one,
    and it sets [L] to its reading; every later one sets [L] to the larger of [L] plus the
    chunk it credits and its reading, and never above [max_safe]. Every clock read records
    [L] as it is. The invariant states this of the applied samples the trace records, and
    that nothing reads the clock before the first sample. *)

From Coq Require Import List ZArith Bool Arith Lia Sorting.
From Durable Require Import Runtime Exec Rev3 Statements TimeBase TimeStep.
Import ListNotations.
Open Scope Z_scope.

(** ** The shape of the applied samples *)

(** [L] after the last applied sample, or 0 before the first. *)
Definition time_lastl (a : list (Z * Z * Z)) : Z := last (map lafter a) 0.

(** The first applied sample sets [L] to its reading and credits nothing; each later one
    sets [L] by the time rule with a chunk that is not negative; none exceeds [max_safe]. *)
Definition time_shape (a : list (Z * Z * Z)) : Prop :=
  (forall e, nth_error a 0 = Some e -> lafter e = reading e /\ chunk e = 0) /\
  (forall i e e', nth_error a i = Some e -> nth_error a (S i) = Some e' ->
     lafter e' = Z.max (lafter e + chunk e') (reading e') /\ 0 <= chunk e') /\
  (forall e, In e a -> lafter e <= max_safe).

Lemma time_lastl_nth : forall a i e,
  nth_error a i = Some e -> S i = length a -> time_lastl a = lafter e.
Proof.
  intros a i e H L. destruct (exists_last (l := a)) as [a' [z ->]].
  { intros ->. discriminate. }
  rewrite length_app in L. simpl in L.
  rewrite nth_error_app2 in H by lia. replace (i - length a')%nat with 0%nat in H by lia.
  inversion H; subst. unfold time_lastl. rewrite map_app. apply last_last.
Qed.

Lemma time_lastl_snoc : forall a e, time_lastl (a ++ [e]) = lafter e.
Proof. intros. unfold time_lastl. rewrite map_app. apply last_last. Qed.

Lemma time_shape_nil : time_shape [].
Proof.
  split; [intros e H; destruct e; discriminate|].
  split; [intros i e e' H; destruct i; discriminate|]. intros e [].
Qed.

Lemma time_shape_snoc : forall a e,
  time_shape a ->
  (a = [] -> lafter e = reading e /\ chunk e = 0) ->
  (a <> [] -> lafter e = Z.max (time_lastl a + chunk e) (reading e) /\ 0 <= chunk e) ->
  lafter e <= max_safe ->
  time_shape (a ++ [e]).
Proof.
  intros a e [H0 [HS HM]] Hn Hc Hm. split; [|split].
  - intros e1 H. destruct a as [|b a].
    + simpl in H. inversion H; subst. apply Hn. reflexivity.
    + apply H0. exact H.
  - intros i e1 e2 H1 H2.
    assert (Hi : (S i <= length a)%nat).
    { destruct (le_lt_dec (S i) (length a)) as [l|l]; [exact l|].
      rewrite nth_error_app2 in H2 by lia.
      destruct (S i - length a)%nat as [|m] eqn:E; [lia|]. simpl in H2.
      destruct m; discriminate. }
    rewrite nth_error_app1 in H1 by lia.
    destruct (Nat.eq_dec (S i) (length a)) as [Eq|Ne].
    + rewrite nth_error_app2 in H2 by lia. rewrite Eq, Nat.sub_diag in H2.
      inversion H2; subst. rewrite <- (time_lastl_nth a i e1 H1 Eq).
      apply Hc. intros ->. discriminate.
    + rewrite nth_error_app1 in H2 by lia. eapply HS; eauto.
  - intros e1 H. apply in_app_or in H as [H|[<-|[]]]; [apply HM; exact H|exact Hm].
Qed.

(** ** The invariant *)

Record time_invl (x : XState) : Prop := {
  tl_viol : violated x = true -> phase x <> POpen;
  tl_init : phase x = POpen ->
    (applied (trace x) = [] <-> exists c, sub x = Some (SSample c FInitial));
  tl_empty : phase x = POpen -> applied (trace x) = [] ->
    queue x = [] /\ waiter x = None /\ lvalues (trace x) = [];
  tl_logical : logical x = time_lastl (applied (trace x));
  tl_shape : time_shape (applied (trace x));
  tl_sorted : Sorted Z.le (lvalues (trace x));
  tl_below : Forall (fun v => v <= logical x) (lvalues (trace x))
}.

(** Inside a task: the initial sample has been applied, if the attempt is open. *)
Definition time_ctxl (x : XState) : Prop :=
  time_invl x /\ (phase x = POpen -> applied (trace x) <> []).

(** An action that is neither an applied sample nor a clock read. *)
Definition time_is_lval (a : Action) : bool :=
  match a with ASampled _ _ _ _ | AClock _ _ => true | _ => false end.

Lemma time_applied_other : forall t a,
  time_is_lval a = false -> applied (t ++ [a]) = applied t.
Proof.
  intros t a H. rewrite time_applied_app. destruct a; try discriminate; cbn;
    apply app_nil_r.
Qed.

Lemma time_lvalues_other : forall t a,
  time_is_lval a = false -> lvalues (t ++ [a]) = lvalues t.
Proof.
  intros t a H. rewrite time_lvalues_app. destruct a; try discriminate; cbn;
    apply app_nil_r.
Qed.

Lemma time_invl_frame : forall x x',
  time_invl x ->
  applied (trace x') = applied (trace x) ->
  lvalues (trace x') = lvalues (trace x) ->
  logical x' = logical x ->
  (violated x' = true -> phase x' <> POpen) ->
  (phase x' = POpen ->
     phase x = POpen /\
     ((exists c, sub x' = Some (SSample c FInitial)) <->
      (exists c, sub x = Some (SSample c FInitial))) /\
     (applied (trace x) = [] -> queue x' = [] /\ waiter x' = None)) ->
  time_invl x'.
Proof.
  intros x x' Hx A Lv Lg V P. constructor.
  - exact V.
  - intros Ho. destruct (P Ho) as [Ho' [Hi _]]. rewrite A, Hi. apply (tl_init x Hx Ho').
  - intros Ho He. destruct (P Ho) as [Ho' [_ Hq]]. rewrite A in He.
    destruct (Hq He) as [Q W]. split; [exact Q|]. split; [exact W|].
    rewrite Lv. apply (tl_empty x Hx Ho' He).
  - rewrite Lg, A. apply (tl_logical x Hx).
  - rewrite A. apply (tl_shape x Hx).
  - rewrite Lv. apply (tl_sorted x Hx).
  - rewrite Lv, Lg. apply (tl_below x Hx).
Qed.

Lemma time_ctxl_frame : forall x x',
  time_ctxl x ->
  applied (trace x') = applied (trace x) ->
  lvalues (trace x') = lvalues (trace x) ->
  logical x' = logical x ->
  (violated x' = true -> phase x' <> POpen) ->
  (phase x' = POpen -> phase x = POpen /\ forall c, sub x' <> Some (SSample c FInitial)) ->
  time_ctxl x'.
Proof.
  intros x x' [Hx Hc] A Lv Lg V P. split.
  - apply (time_invl_frame x x' Hx A Lv Lg V). intros Ho.
    destruct (P Ho) as [Ho' Hs]. split; [exact Ho'|]. split.
    + split; intros [c Hc']; [exfalso; exact (Hs c Hc')|].
      exfalso. apply (Hc Ho'). apply (tl_init x Hx Ho'). exists c. exact Hc'.
    + intros He. exfalso. exact (Hc Ho' He).
  - intros Ho. destruct (P Ho) as [Ho' _]. rewrite A. apply Hc. exact Ho'.
Qed.

(** The common case: some actions that are not samples or clock reads are appended, and the
    subscription is not the initial sample. *)
Lemma time_ctxl_simple : forall x x' new,
  time_ctxl x ->
  trace x' = trace x ++ new -> forallb (fun a => negb (time_is_lval a)) new = true ->
  logical x' = logical x ->
  (violated x' = true -> phase x' <> POpen) ->
  (phase x' = POpen -> phase x = POpen /\ forall c, sub x' <> Some (SSample c FInitial)) ->
  time_ctxl x'.
Proof.
  intros x x' new Hx T N Lg V P. apply (time_ctxl_frame x x' Hx); auto.
  - rewrite T. clear T. induction new as [|a new IH] using rev_ind;
      [rewrite app_nil_r; reflexivity|].
    rewrite forallb_app in N. apply andb_true_iff in N as [N1 N2]. simpl in N2.
    rewrite andb_true_r, negb_true_iff in N2.
    rewrite app_assoc, time_applied_other by exact N2. apply IH. exact N1.
  - rewrite T. clear T. induction new as [|a new IH] using rev_ind;
      [rewrite app_nil_r; reflexivity|].
    rewrite forallb_app in N. apply andb_true_iff in N as [N1 N2]. simpl in N2.
    rewrite andb_true_r, negb_true_iff in N2.
    rewrite app_assoc, time_lvalues_other by exact N2. apply IH. exact N1.
Qed.

Lemma time_ctxl_not_initial : forall x,
  time_ctxl x -> phase x = POpen -> forall c, sub x <> Some (SSample c FInitial).
Proof.
  intros x [Hx Hc] Ho c Hs. apply (Hc Ho). apply (tl_init x Hx Ho). exists c. exact Hs.
Qed.

(** ** Helpers inside a task *)

Lemma time_ctxl_violate : forall x v, time_ctxl x -> time_ctxl (violate x v).
Proof.
  intros x v Hx. destruct (time_violate_fields x v (tl_viol x (proj1 Hx)))
    as [V [Lg [Ph [_ [T|T]]]]].
  - apply (time_ctxl_simple x _ [] Hx); auto. rewrite app_nil_r. exact T.
    intros Ho; contradiction.
  - apply (time_ctxl_simple x _ [AViolation v] Hx); auto. intros Ho; contradiction.
Qed.

Lemma time_ctxl_close : forall x c, time_ctxl x -> time_ctxl (close x c).
Proof.
  intros x c Hx. destruct (time_close_fields x c) as [T [Lg [V [Op Cl]]]].
  assert (Ph : phase (close x c) <> POpen).
  { destruct (phase x) eqn:E.
    - rewrite (proj1 (Op eq_refl)). discriminate.
    - apply Cl. discriminate.
    - apply Cl. discriminate. }
  apply (time_ctxl_simple x _ [] Hx); auto. rewrite app_nil_r. exact T.
  intros Ho; contradiction.
Qed.

Lemma time_ctxl_finish : forall x v, time_ctxl x -> time_ctxl (finish x v).
Proof.
  intros x v Hx. apply (time_ctxl_simple x _ [AExit v] Hx); auto; cbn; discriminate.
Qed.

Lemma time_ctxl_issue : forall I x k o s,
  time_ctxl x -> (forall c c', s c <> SSample c' FInitial) -> time_ctxl (issue I x k o s).
Proof.
  intros I x k o s Hx Hs. destruct (time_issue_cases I x k o s) as [-> | ->].
  - apply time_ctxl_finish. exact Hx.
  - apply (time_ctxl_simple x _ [ACommand (next_cmd x) k o] Hx); cbn; auto.
    + apply (tl_viol x (proj1 Hx)).
    + intros Ho. split; [exact Ho|]. intros c E. inversion E. apply (Hs _ _ H0).
Qed.

Lemma time_ctxl_issue_op : forall I x f tok op,
  time_ctxl x -> time_ctxl (issue_op I x f tok op).
Proof.
  intros I x f tok op Hx. unfold issue_op. destruct op.
  - apply time_ctxl_issue; [exact Hx|]. discriminate.
  - destruct (match d with Millis m => split m | Forever => (max_chunk, Endless) end).
    apply time_ctxl_issue; [exact Hx|]. discriminate.
Qed.

(** A change to fields other than the trace, [L], the latch, the phase and the
    subscription. *)
Lemma time_ctxl_fields : forall x x',
  time_ctxl x -> trace x' = trace x -> logical x' = logical x ->
  violated x' = violated x -> phase x' = phase x -> sub x' = sub x -> time_ctxl x'.
Proof.
  intros x x' Hx T Lg V P S. apply (time_ctxl_simple x _ [] Hx); auto.
  - rewrite app_nil_r. exact T.
  - rewrite V, P. apply (tl_viol x (proj1 Hx)).
  - intros Ho. rewrite P in Ho. split; [exact Ho|]. rewrite S.
    apply time_ctxl_not_initial; assumption.
Qed.

Lemma time_ctxl_emit : forall x a,
  time_ctxl x -> time_is_lval a = false -> time_ctxl (emit x a).
Proof.
  intros x a Hx N. apply (time_ctxl_simple x _ [a] Hx); cbn; auto.
  - rewrite N. reflexivity.
  - apply (tl_viol x (proj1 Hx)).
  - intros Ho. split; [exact Ho|]. apply time_ctxl_not_initial; assumption.
Qed.

Lemma time_ctxl_on_start : forall I x f tok op,
  time_ctxl x -> time_ctxl (on_start I x f tok op).
Proof.
  intros I x f tok op Hx. unfold on_start. destruct (phase x) eqn:Ph.
  - assert (Hy : time_ctxl (emit x (AStart f tok op))) by (apply time_ctxl_emit; auto).
    destruct (zero_sleep op).
    { unfold enqueue. apply (time_ctxl_fields _ _ Hy); reflexivity. }
    destruct (awaiter (emit x (AStart f tok op))); [apply time_ctxl_violate; exact Hy|].
    destruct (held (emit x (AStart f tok op))).
    { unfold enqueue. apply (time_ctxl_fields _ _ Hy); reflexivity. }
    destruct (slot_held (emit x (AStart f tok op))).
    { apply (time_ctxl_fields _ _ Hy); reflexivity. }
    apply time_ctxl_issue_op. apply (time_ctxl_fields _ _ Hy); reflexivity.
  - unfold enqueue. apply (time_ctxl_fields (emit x (AStart f tok op)));
      [apply time_ctxl_emit; auto|reflexivity..].
  - exact Hx.
Qed.

Lemma time_ctxl_on_release : forall x f tok,
  time_ctxl x -> time_ctxl (on_release x f tok).
Proof.
  intros x f tok Hx.
  assert (Hy : time_ctxl (match phase x with
                          | POpen => set_queue x (filter (fun t => negb (for_token f tok t))
                                                         (queue x))
                          | _ => x end)).
  { destruct (phase x); [apply (time_ctxl_fields _ _ Hx); reflexivity|exact Hx..]. }
  unfold on_release.
  set (y := match phase x with
            | POpen => set_queue x (filter (fun t => negb (for_token f tok t)) (queue x))
            | _ => x end) in *.
  destruct (phase y) eqn:Py; try exact Hy.
  destruct (awaiter y) as [a|]; [|exact Hy].
  destruct (negb (pair_eqb a (f, tok))); [exact Hy|].
  destruct (waiter y).
  - apply (time_ctxl_fields _ _ Hy); reflexivity.
  - destruct (sub y) as [s|] eqn:Sy; [|apply (time_ctxl_fields _ _ Hy); reflexivity].
    destruct (release_sub s) as [[[f' tok'] s']|] eqn:Rs;
      [|apply (time_ctxl_fields _ _ Hy); reflexivity].
    destruct (pair_eqb (f', tok') (f, tok));
      [|apply (time_ctxl_fields _ _ Hy); reflexivity].
    apply (time_ctxl_simple y _ [] Hy); cbn; auto.
    + rewrite app_nil_r. reflexivity.
    + apply (tl_viol y (proj1 Hy)).
    + intros Ho. split; [exact Ho|]. intros c E. inversion E; subst.
      destruct s as [| c0 [] |]; cbn in Rs; inversion Rs.
Qed.

Lemma time_ctxl_on_event : forall I x e, time_ctxl x -> time_ctxl (on_event I x e).
Proof.
  intros I x e Hx. unfold on_event.
  destruct (phase x); try exact Hx;
  (destruct e as [f tok op|f tok|pr t|f|r];
   [apply time_ctxl_on_start; exact Hx
   |apply time_ctxl_on_release; exact Hx
   |destruct (Nat.eqb pr 0);
      [unfold enqueue; apply (time_ctxl_fields _ _ Hx); reflexivity
      |apply time_ctxl_violate; exact Hx]
   |apply (time_ctxl_fields _ _ Hx); reflexivity
   |destruct (root_exit x);
      [apply time_ctxl_violate; exact Hx
      |apply time_ctxl_close; apply (time_ctxl_fields _ _ Hx); reflexivity]]).
Qed.

Lemma time_sorted_snoc : forall l v,
  Sorted Z.le l -> Forall (fun w => w <= v) l -> Sorted Z.le (l ++ [v]).
Proof.
  intros l v. induction l as [|a l IH]; intros S F; cbn.
  - repeat constructor.
  - inversion S; subst. inversion F; subst. constructor; [apply IH; assumption|].
    destruct l as [|b l]; cbn; constructor; [lia|]. inversion H2. exact H0.
Qed.

Lemma time_ctxl_clock : forall x f,
  time_ctxl x ->
  time_ctxl (match phase x with PDone => x | _ => emit x (AClock f (logical x)) end).
Proof.
  intros x f Hx. destruct (phase x) eqn:Ph; try exact Hx;
  (destruct Hx as [Hx Hc];
   assert (A : applied (trace x ++ [AClock f (logical x)]) = applied (trace x))
     by (rewrite time_applied_app; cbn; apply app_nil_r);
   split; [constructor; tsimp; rewrite ?A|tsimp; rewrite A; exact Hc];
   [apply (tl_viol x Hx)
   |apply (tl_init x Hx)
   |intros Ho He; exfalso; exact (Hc Ho He)
   |apply (tl_logical x Hx)
   |apply (tl_shape x Hx)
   |rewrite time_lvalues_app; apply time_sorted_snoc; [apply (tl_sorted x Hx)|apply (tl_below x Hx)]
   |rewrite time_lvalues_app; apply Forall_app; split;
      [apply (tl_below x Hx)|constructor; [lia|constructor]]]).
Qed.

Lemma time_ctxl_draw : forall I x f,
  time_ctxl x ->
  time_ctxl (match phase x with
             | PDone => x
             | _ => emit (set_draws x (S (draws x))) (ADraw f (stream I (draws x)))
             end).
Proof.
  intros I x f Hx. destruct (phase x); try exact Hx;
    (apply time_ctxl_emit; [apply (time_ctxl_fields _ _ Hx); reflexivity|reflexivity]).
Qed.

Lemma time_ctxl_interp : forall I X (s : Script X) x,
  time_ctxl x -> time_ctxl (fst (interp I x s)).
Proof.
  intros I. apply time_interp_ind.
  - apply time_ctxl_on_event.
  - apply time_ctxl_clock.
  - apply time_ctxl_draw.
  - intros x f Hx. apply (time_ctxl_fields _ _ Hx); reflexivity.
Qed.

(** ** Steps *)

Lemma time_nolval_app : forall t new,
  forallb (fun a => negb (time_is_lval a)) new = true ->
  applied (t ++ new) = applied t /\ lvalues (t ++ new) = lvalues t.
Proof.
  intros t new N. induction new as [|a new IH] using rev_ind;
    [rewrite app_nil_r; auto|].
  rewrite forallb_app in N. apply andb_true_iff in N as [N1 N2]. simpl in N2.
  rewrite andb_true_r, negb_true_iff in N2. rewrite app_assoc.
  rewrite time_applied_other, time_lvalues_other by exact N2. apply IH. exact N1.
Qed.

(** The attempt leaves the open phase, and no sample or clock read is recorded. *)
Lemma time_invl_leave : forall x x' new,
  time_invl x -> trace x' = trace x ++ new ->
  forallb (fun a => negb (time_is_lval a)) new = true ->
  logical x' = logical x -> phase x' <> POpen -> time_invl x'.
Proof.
  intros x x' new Hx T N Lg P. destruct (time_nolval_app (trace x) new N) as [A Lv].
  apply (time_invl_frame x x' Hx); rewrite ?T; auto; intros; contradiction.
Qed.

Lemma time_invl_fields : forall x x',
  time_invl x -> trace x' = trace x -> logical x' = logical x ->
  violated x' = violated x -> phase x' = phase x -> sub x' = sub x ->
  queue x' = queue x -> waiter x' = waiter x -> time_invl x'.
Proof.
  intros x x' Hx T Lg V P S Q W.
  apply (time_invl_frame x x' Hx); rewrite ?T; auto.
  - rewrite V, P. apply (tl_viol x Hx).
  - intros Ho. rewrite P in Ho. split; [exact Ho|]. rewrite S. split; [tauto|].
    rewrite Q, W. intros He. destruct (tl_empty x Hx Ho He) as [A [B _]]. auto.
Qed.

Lemma time_invl_violate : forall x v, time_invl x -> time_invl (violate x v).
Proof.
  intros x v Hx. destruct (time_violate_fields x v (tl_viol x Hx)) as [V [Lg [Ph [_ [T|T]]]]].
  - apply (time_invl_leave x _ [] Hx); auto. rewrite app_nil_r. exact T.
  - apply (time_invl_leave x _ [AViolation v] Hx); auto.
Qed.

Lemma time_ctxl_of_invl : forall x,
  time_invl x -> (phase x = POpen -> forall c, sub x <> Some (SSample c FInitial)) ->
  time_ctxl x.
Proof.
  intros x Hx Hs. split; [exact Hx|]. intros Ho He.
  destruct (proj1 (tl_init x Hx Ho) He) as [c Hc]. exact (Hs Ho c Hc).
Qed.

Lemma time_ctxl_run_head : forall R I x r t rest,
  time_invl x -> queue x = t :: rest -> time_invl (fst (run_head R I x r t rest)).
Proof.
  intros R I x r t rest Hx Q.
  assert (Hc : time_ctxl x).
  { split; [exact Hx|]. intros Ho He. destruct (tl_empty x Hx Ho He) as [E _].
    rewrite Q in E. discriminate. }
  unfold run_head. apply time_ctxl_interp.
  assert (H0 : time_ctxl (set_progress (set_queue x rest) (S (progress x))))
    by (apply (time_ctxl_fields _ _ Hc); reflexivity).
  set (x0 := set_progress (set_queue x rest) (S (progress x))) in *.
  assert (H1 : time_ctxl (match task_action t with Some a => emit x0 a | None => x0 end)).
  { destruct t; cbn; try exact H0; apply time_ctxl_emit; auto. }
  set (x1 := match task_action t with Some a => emit x0 a | None => x0 end) in *.
  destruct t; try exact H1; destruct (awaiter x1) as [a|]; try exact H1;
    destruct (pair_eqb a _); try exact H1; apply (time_ctxl_fields _ _ H1); reflexivity.
Qed.

(** Applying a sample, and what follows it. *)
Lemma time_invl_apply : forall I x c v after,
  time_invl x -> phase x = POpen -> sub x = Some (SSample c after) ->
  (forall f tok k, after <> FReleased f tok k) ->
  time_invl (let x1 := apply_sample x c v after in
             match phase x1 with POpen => after_sample I x1 after | _ => x1 end).
Proof.
  intros I x c v after Hx Ho Hs Hr. cbv zeta.
  assert (Vf : violated x = false).
  { destruct (violated x) eqn:V; [|reflexivity]. exfalso. exact (tl_viol x Hx V Ho). }
  unfold apply_sample.
  set (credit := match after with
                 | FLink f tok k _ => if 0 <? k then Some (f, tok, k) else None
                 | _ => None end).
  set (floor := match credit with Some (_, _, k) => k | None => 0 end).
  set (l := match after with FInitial => v | _ => Z.max (logical x + floor) v end).
  destruct (max_safe <? l) eqn:Ov.
  - pose proof (time_invl_violate x Overflow Hx) as Hv.
    destruct (time_violate_fields x Overflow (tl_viol x Hx)) as [_ [_ [Ph _]]].
    destruct (phase (violate x Overflow)); [contradiction|exact Hv..].
  - assert (Fl : 0 <= floor).
    { subst floor credit. destruct after as [|? ? ?|? ? k ?|? ?|? ? ?]; try lia.
      destruct (0 <? k) eqn:K; [|lia].
      apply Z.ltb_lt in K. lia. }
    assert (Ch : (fun cr : option (FiberId * Token * Z) =>
                   match cr with Some (_, _, k) => k | None => 0 end) credit = floor)
      by reflexivity.
    set (x1 := set_sub (set_logical (emit x (ASampled c v l credit)) l) None).
    assert (A1 : applied (trace x1) = applied (trace x) ++ [(v, l, floor)])
      by (subst x1; tsimp; rewrite time_applied_app; reflexivity).
    assert (Hc1 : time_ctxl x1).
    { split; [constructor|]; subst x1; tsimp; rewrite ?A1.
      - intros V. rewrite Vf in V. discriminate.
      - intros _. split; [intros E; apply app_eq_nil in E as [_ E]; discriminate|].
        intros [c' E]; discriminate.
      - intros _ E. apply app_eq_nil in E as [_ E]. discriminate.
      - rewrite time_lastl_snoc. reflexivity.
      - apply time_shape_snoc.
        + apply (tl_shape x Hx).
        + intros E. destruct (proj1 (tl_init x Hx Ho) E) as [c' E'].
          rewrite Hs in E'. inversion E'; subst. cbn. split; reflexivity.
        + intros E. assert (NI : after <> FInitial).
          { intros ->. apply E. apply (tl_init x Hx Ho). exists c. exact Hs. }
          cbn. rewrite <- (tl_logical x Hx). split; [|exact Fl].
          subst l. destruct after; try reflexivity. contradiction.
        + cbn. apply Z.ltb_ge in Ov. lia.
      - rewrite time_lvalues_app. cbn.
        destruct (applied (trace x)) eqn:E.
        + destruct (tl_empty x Hx Ho E) as [_ [_ ->]]. repeat constructor.
        + apply time_sorted_snoc; [apply (tl_sorted x Hx)|].
          assert (NI : after <> FInitial).
          { intros ->. assert (E' : applied (trace x) = []).
            { apply (tl_init x Hx Ho). exists c. exact Hs. } congruence. }
          eapply Forall_impl; [|apply (tl_below x Hx)]. intros w Hw. cbn in Hw.
          subst l. destruct after; try contradiction; lia.
      - rewrite time_lvalues_app. cbn. apply Forall_app. split; [|repeat constructor; lia].
        destruct (applied (trace x)) eqn:E.
        + destruct (tl_empty x Hx Ho E) as [_ [_ ->]]. constructor.
        + assert (NI : after <> FInitial).
          { intros ->. assert (E' : applied (trace x) = []).
            { apply (tl_init x Hx Ho). exists c. exact Hs. } congruence. }
          eapply Forall_impl; [|apply (tl_below x Hx)]. intros w Hw. cbn in Hw.
          subst l. destruct after; try contradiction; lia.
      - intros _ E. apply app_eq_nil in E as [_ E]. discriminate. }
    assert (P1 : phase x1 = POpen) by (subst x1; tsimp; exact Ho).
    rewrite P1. enough (G : time_ctxl (after_sample I x1 after)) by exact (proj1 G).
    destruct after as [|f tok o|f tok k rest|f tok|f tok k];
      cbn [after_sample]; unfold enqueue.
    + apply (time_ctxl_fields _ _ Hc1); reflexivity.
    + apply (time_ctxl_fields _ _ Hc1); reflexivity.
    + destruct (link_of rest) as [[ch rest']|].
      * apply time_ctxl_issue; [exact Hc1|discriminate].
      * apply (time_ctxl_fields _ _ Hc1); reflexivity.
    + apply (time_ctxl_fields _ _ Hc1); reflexivity.
    + exfalso. apply (Hr f tok k). reflexivity.
Qed.

Lemma time_invl_of_ctxl : forall x, time_ctxl x -> time_invl x.
Proof. intros x [H _]. exact H. Qed.

(** A notification for the subscription. *)
Lemma time_invl_notify : forall I x s r,
  time_invl x -> phase x = POpen -> sub x = Some s -> time_invl (on_notify I x s r).
Proof.
  intros I x s r Hx Ph Hs.
  destruct s as [c0 f0 tok0 op0 k0 rest0|c0 [|f0 tok0 o0|f0 tok0 k0 rest0|f0 tok0|f0 tok0 k0]|c0];
    [|destruct r as [o|v|]; cbn [on_notify];
      [exact Hx|apply (time_invl_apply I x); auto; intros; discriminate
      |apply time_invl_violate; exact Hx]|..].
  all: assert (Hc : time_ctxl x) by (apply time_ctxl_of_invl; [exact Hx|];
    intros _ c E; rewrite Hs in E; discriminate).
  all: destruct r as [o|v|]; cbn [on_notify];
    try (destruct op0 as [? ?|?]); cbn [on_notify issue_sample];
    try (apply time_invl_of_ctxl; apply time_ctxl_issue; [exact Hc|discriminate]);
    try (apply time_invl_of_ctxl; apply (time_ctxl_fields _ _ Hc); reflexivity);
    try (apply time_invl_violate; exact Hx);
    try (apply (time_invl_apply I x); [exact Hx|exact Ph|exact Hs|intros; discriminate]).
  all: apply time_invl_of_ctxl; apply (time_ctxl_simple x _ [] Hc); tsimp; auto;
    [rewrite app_nil_r; reflexivity|apply (tl_viol x Hx)|intros _; split; [exact Ph|];
     discriminate].
Qed.

(** The cancel signal, observed through the subscription. *)
Lemma time_invl_cancel : forall I x s,
  time_invl x -> phase x = POpen -> sub x = Some s -> time_invl (on_cancel I x s).
Proof.
  intros I x s Hx Ph Hs.
  destruct s as [c0 f0 tok0 op0 k0 rest0|c0 [|f0 tok0 o0|f0 tok0 k0 rest0|f0 tok0|f0 tok0 k0]|c0].
  2: { cbn [on_cancel issue_sample].
       assert (Ae : applied (trace x) = []) by (apply (tl_init x Hx Ph); exists c0; exact Hs).
       destruct (tl_empty x Hx Ph Ae) as [Qe [We Le]].
       unfold issue_sample. match goal with |- context [issue ?I ?y ?k ?o ?s] =>
         destruct (time_issue_cases I y k o s) as [-> | ->] end.
       - apply (time_invl_leave x _ [AExit VMismatch] Hx); auto. unfold finish. tsimp.
         discriminate.
       - apply (time_invl_frame x _ Hx); tsimp.
         + rewrite time_applied_app. cbn. apply app_nil_r.
         + rewrite time_lvalues_app. cbn. apply app_nil_r.
         + reflexivity.
         + intros V. apply (tl_viol x Hx V).
         + intros _. split; [exact Ph|]. split; [split; intros _; eauto|].
           intros _. split; assumption. }
  all: assert (Hc : time_ctxl x) by (apply time_ctxl_of_invl; [exact Hx|];
    intros _ c E; rewrite Hs in E; discriminate).
  all: cbn [on_cancel issue_sample]; apply time_invl_of_ctxl;
    try (apply time_ctxl_issue; [exact Hc|discriminate]).
  all: apply (time_ctxl_simple x _ [] Hc); tsimp; auto;
    [rewrite app_nil_r; reflexivity|apply (tl_viol x Hx)|intros _; split; [exact Ph|];
     discriminate].
Qed.

Lemma time_invl_boundary : forall I Sch x x',
  time_invl x -> queue x = [] -> at_boundary I Sch x = Some x' -> time_invl x'.
Proof.
  intros I Sch x x' Hx Q E. unfold at_boundary in E.
  destruct (phase x) eqn:Ph; try discriminate.
  2: { inversion E; subst. apply (time_invl_leave x _ [AExit (verdict x)] Hx); auto.
       unfold finish. tsimp. discriminate. }
  assert (Hc : (forall c, sub x <> Some (SSample c FInitial)) -> time_ctxl x).
  { intros Hs. apply time_ctxl_of_invl; [exact Hx|]. intros _. exact Hs. }
  destruct (held x) eqn:Hh, (waiter x) as [[[f tok] op]|] eqn:Hw.
  1: { inversion E; subst. assert (Ne : applied (trace x) <> []).
    { intros He. destruct (tl_empty x Hx Ph He) as [_ [W _]]. congruence. }
    apply time_ctxl_of_invl in Hx as Hc'; [|intros _ c Hs; apply Ne;
      apply (tl_init x Hx Ph); exists c; exact Hs].
    unfold enqueue. apply time_invl_of_ctxl. apply (time_ctxl_fields _ _ Hc'); reflexivity. }
  all: destruct (sub x) as [s|] eqn:Hs;
    [|inversion E; subst;
      first [apply time_invl_violate; exact Hx
            |apply time_invl_of_ctxl; apply time_ctxl_issue_op;
             apply (time_ctxl_fields _ _ (Hc ltac:(congruence))); reflexivity]].
  all: unfold at_boundary_sub in E;
    destruct (arrived Sch (micro x) <=? cursor x)%nat; [discriminate|];
    destruct (nth_error (entries I) (cursor x)) as [[c r|]|]; try discriminate;
    [destruct (Nat.eqb c (sub_cmd s));
      [|destruct (c <? next_cmd x)%nat; inversion E; subst;
        apply (time_invl_fields _ _ Hx); reflexivity]
    |].
  all: inversion E; subst; clear E.
  all: first [apply time_invl_notify | apply time_invl_cancel];
    try (apply (time_invl_fields _ _ Hx); reflexivity); tsimp; assumption.
Qed.

Lemma time_invl_step : forall R I Sch s,
  time_invl (xs s) -> time_invl (xs (step R I Sch s)).
Proof.
  intros R I Sch s Hx. unfold step. cbv zeta.
  destruct (phase (xs s)) eqn:Ph; try exact Hx.
  all: destruct (stop_due Sch (xs s));
   [tsimp; apply (time_invl_leave (xs s) _ [] Hx); tsimp; rewrite ?app_nil_r; auto;
    discriminate|].
  all: destruct (foreign_due I (xs s)) as [fi|];
   [tsimp; apply (time_invl_fields (on_foreign (set_fseen (xs s) (Some (progress (xs s)))) fi));
    try reflexivity; destruct fi; cbn [on_foreign]; try apply time_invl_violate;
    apply (time_invl_fields _ _ Hx); reflexivity|].
  all: destruct (cut_due Sch (xs s)) as [k|];
   [tsimp; apply (time_invl_fields (on_cut (xs s) k)); try reflexivity;
    unfold on_cut; destruct k;
    [| |apply (time_invl_leave (xs s) _ [ACut Crashed] Hx); tsimp; auto; discriminate];
    match goal with |- time_invl (close (emit ?y ?a) ?c) =>
      destruct (time_close_fields (emit y a) c) as [T [L [V [Op Cl]]]];
      apply (time_invl_leave (xs s) _ [a] Hx); auto end;
    tsimp;
    first [rewrite (proj1 (Op Ph)); discriminate | apply Cl; rewrite Ph; discriminate]
   |].
  all: destruct (queue (xs s)) as [|t rest] eqn:Q;
   [destruct (at_boundary I Sch (xs s)) as [x'|] eqn:B; tsimp;
    [apply (time_invl_fields x'); try reflexivity; eapply time_invl_boundary; eauto
    |apply (time_invl_fields (xs s)); try reflexivity; exact Hx]
   |destruct (run_head R I (xs s) (rs s) t rest) as [x' r'] eqn:E; tsimp;
    apply (time_invl_fields x'); try reflexivity;
    replace x' with (fst (run_head R I (xs s) (rs s) t rest)) by (rewrite E; reflexivity);
    apply time_ctxl_run_head; assumption].
Qed.

Lemma time_invl_initial : forall R p I, time_invl (xs (initial R p I)).
Proof.
  intros R p I. unfold initial. tsimp. unfold issue_sample.
  match goal with |- context [issue ?I ?y ?k ?o ?s] =>
    destruct (time_issue_cases I y k o s) as [-> | ->] end.
  - constructor; unfold finish; tsimp; try discriminate; cbn; try reflexivity.
    + apply time_shape_nil.
    + constructor.
    + constructor.
  - constructor; tsimp; try discriminate; cbn; try reflexivity.
    + intros _. split; [intros _; eauto|reflexivity].
    + intros _ _. auto.
    + apply time_shape_nil.
    + constructor.
    + constructor.
Qed.

Lemma time_iterate_S : forall R I Sch n s,
  iterate R I Sch (S n) s = step R I Sch (iterate R I Sch n s).
Proof.
  intros R I Sch n. induction n as [|n IH]; intros s; [reflexivity|].
  change (iterate R I Sch (S (S n)) s) with (iterate R I Sch (S n) (step R I Sch s)).
  rewrite IH. reflexivity.
Qed.

(** The invariant holds of every state an attempt reaches. *)
Lemma time_invl_run : forall R p I Sch n,
  time_invl (xs (iterate R I Sch n (initial R p I))).
Proof.
  intros R p I Sch n. induction n as [|n IH]; [apply time_invl_initial|].
  rewrite time_iterate_S. apply time_invl_step. exact IH.
Qed.
