(** * Arrival: facts the proof of S2 needs about cursors, commands and cuts. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Statements ArrivalBase ArrivalMicro ArrivalExt
  ArrivalGrow ArrivalSim ArrivalSwap ArrivalSwapStep.
Import ListNotations.
Open Scope Z_scope.

(** ** Lists *)

Lemma arrival_ok_iff : forall t,
  forallb arrival_ok t = true <-> forall c, ~ In (ACut c) t.
Proof.
  induction t as [|a t IH]; cbn; [split; auto|].
  rewrite andb_true_iff, IH. split.
  - intros [H1 H2] c [E|H]; [subst a; discriminate|exact (H2 c H)].
  - intros H. split; [|intros c Hc; apply (H c); right; exact Hc].
    destruct a; try reflexivity. exfalso. eapply H. left. reflexivity.
Qed.

Lemma arrival_before_cut_prefix : forall t, prefix (before_cut t) t.
Proof.
  induction t as [|a t [r IH]]; [exists []; reflexivity|].
  destruct a; try (exists r; cbn; f_equal; exact IH).
  exists (ACut k :: t). reflexivity.
Qed.

Lemma arrival_before_cut_mono : forall t l, prefix (before_cut t) (before_cut (t ++ l)).
Proof.
  induction t as [|a t IH]; intros l; [exists (before_cut l); reflexivity|].
  destruct (IH l) as [r E].
  destruct a; try (exists r; cbn; f_equal; exact E).
  exists []. reflexivity.
Qed.

Lemma arrival_prefix_trans : forall {X} (a b c : list X), prefix a b -> prefix b c -> prefix a c.
Proof. intros X a b c [r1 E1] [r2 E2]. exists (r1 ++ r2). subst. symmetry. apply app_assoc. Qed.

Lemma arrival_prefix_in : forall {X} (a b : list X) v, prefix a b -> In v a -> In v b.
Proof. intros X a b v [r E] H. subst. apply in_or_app. left. exact H. Qed.

(** ** Commands *)

Lemma arrival_cmd_eqb_refl : forall k, cmd_eqb k k = true.
Proof.
  intros [[kk a|d]|]; cbn; try reflexivity. apply Nat.eqb_refl.
Qed.

Lemma arrival_numbered_nth : forall t n c k o, arrival_numbered n t ->
  In (ACommand c k o) t -> (n <= c)%nat /\ nth_error (commands t) (c - n) = Some k.
Proof.
  induction t as [|a t IH]; intros n c k o H Hin; [destruct Hin|].
  destruct Hin as [E|Hin].
  - subst a. cbn in H. destruct H as [-> _]. rewrite Nat.sub_diag. split; [lia|reflexivity].
  - destruct a; cbn in H |- *; change (flat_map _ t) with (commands t);
      try (apply IH with (o := o); assumption).
    destruct H as [E0 H]. destruct (IH (S n) c k o H Hin) as [L E].
    split; [lia|]. replace (c - n)%nat with (S (c - S n)) by lia. exact E.
Qed.

Lemma arrival_commands_prefix : forall a b, prefix a b -> prefix (commands a) (commands b).
Proof.
  intros a b [r E]. subst. exists (commands r). apply arrival_commands_app.
Qed.

Lemma arrival_nth_prefix : forall {X} (a b : list X) i v w, compatible a b ->
  nth_error a i = Some v -> nth_error b i = Some w -> v = w.
Proof.
  intros X a b i v w [[r E]|[r E]] Ha Hb; subst.
  - rewrite nth_error_app1 in Hb; [congruence|]. apply nth_error_Some. congruence.
  - rewrite nth_error_app1 in Ha; [congruence|]. apply nth_error_Some. congruence.
Qed.

(** A state whose commands agree with [T]'s, where [T] is the persisted journal of [J]. *)
Lemma arrival_agree_nc : forall J y T, arrival_nc y ->
  compatible (trace y) T -> persisted J = commands T -> arrival_agree J (trace y).
Proof.
  intros J y T [N _] C P c k o k' Hin Hp.
  destruct (arrival_numbered_nth _ _ _ _ _ N Hin) as [_ E]. rewrite Nat.sub_0_r in E.
  rewrite P in Hp.
  assert (Cc : compatible (commands (trace y)) (commands T))
    by (destruct C; [left|right]; apply arrival_commands_prefix; assumption).
  rewrite (arrival_nth_prefix _ _ _ _ _ Cc E Hp). apply arrival_cmd_eqb_refl.
Qed.

(** ** The cursor *)

Lemma arrival_ext_cursor : forall I b x y, arrival_ext I b x y -> cursor y = cursor x.
Proof. intros I b x y (_&_&_&_&U&_). exact U. Qed.

Lemma arrival_at_boundary_sub_entry : forall I Sch x sb y,
  at_boundary_sub I Sch x sb = Some y -> exists e, nth_error (entries I) (cursor x) = Some e.
Proof.
  intros I Sch x sb y H. unfold at_boundary_sub in H.
  destruct (arrived Sch (micro x) <=? cursor x)%nat; [discriminate|].
  destruct (nth_error (entries I) (cursor x)) as [e|]; [exists e; reflexivity|discriminate].
Qed.

Lemma arrival_at_boundary_cursor : forall I Sch x y, at_boundary I Sch x = Some y ->
  cursor y = cursor x \/
  (cursor y = S (cursor x) /\ exists e, nth_error (entries I) (cursor x) = Some e).
Proof.
  intros I Sch x y H. unfold at_boundary in H.
  assert (Sub : forall sb, at_boundary_sub I Sch x sb = Some y ->
    cursor y = cursor x \/
    (cursor y = S (cursor x) /\ exists e, nth_error (entries I) (cursor x) = Some e)).
  { intros sb Hy. right. split; [eapply arrival_at_boundary_sub_cursor; eassumption|].
    eapply arrival_at_boundary_sub_entry; eassumption. }
  destruct (phase x); [|injection H as <-; left|discriminate].
  - destruct (held x), (waiter x) as [[[f tok] op]|].
    + injection H as <-. left. reflexivity.
    + destruct (sub x) as [sb|]; [exact (Sub sb H)|].
      injection H as <-. left. eapply arrival_ext_cursor. apply (arrival_violate_ext I).
    + destruct (sub x) as [sb|]; [exact (Sub sb H)|].
      injection H as <-. left.
      transitivity (cursor (set_waiter x None)); [|reflexivity].
      eapply arrival_ext_cursor. apply arrival_issue_op_ext.
    + destruct (sub x) as [sb|]; [exact (Sub sb H)|].
      injection H as <-. left. eapply arrival_ext_cursor. apply (arrival_violate_ext I).
  - eapply arrival_ext_cursor. apply (arrival_finish_verdict_ext I).
Qed.

Lemma arrival_run_head_cursor : forall R I x r t rest,
  cursor (fst (run_head R I x r t rest)) = cursor x.
Proof.
  intros. rewrite arrival_run_head_unfold.
  set (x0 := set_progress (set_queue x rest) (S (progress x))).
  destruct (arrival_interp_ext I (run_task R r t) (arrival_pre x0 t)) as [H _].
  rewrite (arrival_ext_cursor _ _ _ _ H).
  destruct (arrival_pre_ext I x0 t) as [H2 _]. rewrite (arrival_ext_cursor _ _ _ _ H2).
  reflexivity.
Qed.

(** A step under [arrival_sinf] consumes at most the entry at the cursor. *)
Lemma arrival_step_cursor : forall R I s,
  let s' := step R I (arrival_sinf I) s in
  cursor (xs s') = cursor (xs s) \/
  (cursor (xs s') = S (cursor (xs s)) /\
   exists e, nth_error (entries I) (cursor (xs s)) = Some e).
Proof.
  intros R I [x r]. cbn zeta. unfold step. cbn [xs rs].
  destruct (phase x); [| |left; reflexivity];
    cbn [stop_due cut_due arrival_sinf stop_at cut_at];
    (destruct (foreign_due I x) as [fi|];
     [left; cbn [xs]; rewrite arrival_cursor_set_micro;
      transitivity (cursor (set_fseen x (Some (progress x)))); [|reflexivity];
      eapply arrival_ext_cursor; apply (arrival_on_foreign_ext I)|]);
    (destruct (queue x) as [|t rest];
     [|left; pose proof (arrival_run_head_cursor R I x r t rest) as E;
       destruct (run_head R I x r t rest); exact E]);
    (destruct (at_boundary I (arrival_sinf I) x) as [y|] eqn:Hb; [|left; reflexivity]);
    cbn [xs]; rewrite arrival_cursor_set_micro;
    apply (arrival_at_boundary_cursor I (arrival_sinf I) x y Hb).
Qed.

(** ** The run under [arrival_sinf] *)

Lemma arrival_srel_sym : forall R s1 s2, I1 R -> arrival_srel R s1 s2 -> arrival_srel R s2 s1.
Proof. intros R s1 s2 (_&Hs&_) [E Q]. split; [symmetry; exact E|apply Hs; exact Q]. Qed.

Lemma arrival_srel_trans : forall R s1 s2 s3, I1 R ->
  arrival_srel R s1 s2 -> arrival_srel R s2 s3 -> arrival_srel R s1 s3.
Proof.
  intros R s1 s2 s3 (_&_&Ht&_) [E1 Q1] [E2 Q2].
  split; [congruence|eapply Ht; eassumption].
Qed.

Lemma arrival_iterate_add : forall R I Sch a b s,
  iterate R I Sch (a + b) s = iterate R I Sch b (iterate R I Sch a s).
Proof.
  intros R I Sch a. induction a as [|a IH]; intros b s; [reflexivity|].
  cbn [Nat.add iterate]. apply IH.
Qed.

(** A step under [arrival_sinf] that only waits waits for good. *)
Lemma arrival_stuck : forall R I u, I1 R ->
  step R I (arrival_sinf I) u = arrival_bump u ->
  forall m, arrival_srel R (iterate R I (arrival_sinf I) m u) u.
Proof.
  intros R I u HI Hst m. induction m as [|m IH]; [apply arrival_srel_refl; exact HI|].
  rewrite arrival_iterate_S.
  eapply arrival_srel_trans; [exact HI|apply arrival_srel_step; [exact HI|exact IH]|].
  rewrite Hst. split; [reflexivity|]. destruct HI as (H&_). apply H.
Qed.

Lemma arrival_iterate_mono : forall R I k k' s, (k <= k')%nat ->
  (cursor (xs (iterate R I (arrival_sinf I) k s)) <=
   cursor (xs (iterate R I (arrival_sinf I) k' s)))%nat /\
  (progress (xs (iterate R I (arrival_sinf I) k s)) <=
   progress (xs (iterate R I (arrival_sinf I) k' s)))%nat.
Proof.
  intros R I k k' s Hk. induction Hk as [|k' Hk IH]; [split; lia|].
  rewrite arrival_iterate_S.
  destruct (arrival_step_grow R I (arrival_sinf I) (iterate R I (arrival_sinf I) k' s))
    as [(_&_&_&_&U&G) _].
  split; lia.
Qed.

Lemma arrival_iterate_nc : forall R I Sch k s, arrival_nc (xs s) ->
  arrival_nc (xs (iterate R I Sch k s)).
Proof.
  intros R I Sch k. induction k as [|k IH]; intros s H; [exact H|].
  cbn [iterate]. apply IH.
  destruct (arrival_step_grow R I Sch s) as [(_&_&_&N&_) _]. apply N. exact H.
Qed.

(** ** A step under any schedule: a cut, or no cut at all *)

Lemma arrival_step_cut_or_grow : forall R I Sch s, valid_schedule I Sch ->
  (exists c, trace (xs (step R I Sch s)) = trace (xs s) ++ [ACut c] /\
             phase (xs (step R I Sch s)) <> POpen) \/
  arrival_grow I false (xs s) (xs (step R I Sch s)).
Proof.
  intros R I Sch s Hv.
  destruct (arrival_step_cases R I Sch s Hv) as [Hs|[(c&_&Hcut)|[Hw|He]]].
  - right. destruct s as [x r]. cbn [xs] in Hs |- *. unfold step. cbn [xs].
    pose proof (arrival_stop_cut Sch x Hs) as Hc.
    destruct (phase x) as [|[]|] eqn:Hp; try discriminate; rewrite Hs; cbn [xs];
      (eapply arrival_grow_trans; [|apply arrival_grow_micro]);
      (split; [exists []; rewrite app_nil_r; split; [reflexivity|split; [reflexivity|]]
                 ; cbn; discriminate|]);
      cbn; rewrite Hp; cbn; (split; [lia|split; [discriminate|split; [tauto|split; lia]]]).
  - left. exists c. rewrite Hcut. cbn [xs].
    rewrite arrival_trace_set_micro, arrival_phase_set_micro.
    destruct (arrival_on_cut_fields (xs s) c) as (E&_).
    split; [exact E|apply arrival_on_cut_closed].
  - right. rewrite Hw. apply arrival_grow_micro.
  - right. rewrite He. apply (arrival_step_grow R I (arrival_sinf I) s); reflexivity.
Qed.

(** Under any schedule, from a state with no cut, a journal mismatch is only ever reported
    before the cut. *)
Lemma arrival_mm_before_cut : forall R I Sch s0, valid_schedule I Sch ->
  forallb arrival_ok (trace (xs s0)) = true -> forall n,
  let s := iterate R I Sch n s0 in
  ((exists c, In (ACut c) (trace (xs s))) -> phase (xs s) <> POpen) /\
  (In (AExit VMismatch) (trace (xs s)) -> In (AExit VMismatch) (before_cut (trace (xs s)))).
Proof.
  intros R I Sch s0 Hv H0 n. induction n as [|n [IH1 IH2]]; cbn zeta in *.
  - split; [intros [c Hc]; exfalso; apply arrival_ok_iff with (c := c) in H0; contradiction|].
    rewrite arrival_before_cut_ok by exact H0. auto.
  - rewrite arrival_iterate_S. set (s := iterate R I Sch n s0) in *.
    destruct (arrival_step_cut_or_grow R I Sch s Hv) as [(c&E&P)|((l&E&O&M)&P&_)];
      rewrite E.
    + split; [intros _; exact P|]. intros Hm. apply in_app_iff in Hm as [Hm|Hm].
      * eapply arrival_prefix_in; [apply arrival_before_cut_mono|]. apply IH2. exact Hm.
      * destruct Hm as [Hm|[]]. discriminate.
    + specialize (O eq_refl). split.
      * intros [c Hc]. apply in_app_iff in Hc as [Hc|Hc];
          [|apply arrival_ok_iff with (c := c) in O; contradiction].
        intros Hq. apply (IH1 (ex_intro _ c Hc)). rewrite Hq in P.
        destruct (phase (xs s)); cbn in P; [reflexivity|lia|lia].
      * intros Hm. apply in_app_iff in Hm as [Hm|Hm].
        -- eapply arrival_prefix_in; [apply arrival_before_cut_mono|]. apply IH2. exact Hm.
        -- assert (Hx : existsb arrival_mm l = true)
             by (apply existsb_exists; exists (AExit VMismatch); split; auto).
           destruct (M Hx) as [Hp _].
           assert (Ht : forallb arrival_ok (trace (xs s)) = true).
           { apply arrival_ok_iff. intros c Hc. exact (IH1 (ex_intro _ c Hc) Hp). }
           rewrite arrival_before_cut_ok; [apply in_or_app; right; exact Hm|].
           rewrite forallb_app, Ht, O. reflexivity.
Qed.
