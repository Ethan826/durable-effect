(** * Arrival: a run under any schedule follows the run under [arrival_sinf].

    Each step under a valid schedule either waits (only the counter moves), cuts, stops a
    closing after a cut, or takes exactly the step [arrival_sinf] takes. Steps under
    [arrival_sinf] respect [arrival_srel]: the counter is never read, and equivalent runtime
    states give related scripts (I1). So until it is cut, a run is related to the run under
    [arrival_sinf] after the number of steps that acted; after the cut its trace up to the
    cut no longer changes. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Statements ArrivalBase ArrivalMicro ArrivalExt
  ArrivalGrow.
Import ListNotations.
Open Scope Z_scope.

(** ** Equivalent runtime states *)

Lemma arrival_interp_rel : forall {S} (eqv : S -> S -> Prop) I s1 s2,
  script_rel eqv s1 s2 -> forall x,
  fst (interp I x s1) = fst (interp I x s2) /\ eqv (snd (interp I x s1)) (snd (interp I x s2)).
Proof.
  intros S eqv I s1 s2 H. induction H as [a b|e k1 k2 _ IH|f k1 k2 _ IH|f k1 k2 _ IH
    |f k1 k2 _ IH]; intros x; cbn [interp]; auto.
Qed.

Lemma arrival_step_rel : forall R I Sch x r1 r2, I1 R -> requiv R r1 r2 ->
  xs (step R I Sch {| xs := x; rs := r1 |}) = xs (step R I Sch {| xs := x; rs := r2 |}) /\
  requiv R (rs (step R I Sch {| xs := x; rs := r1 |}))
    (rs (step R I Sch {| xs := x; rs := r2 |})).
Proof.
  intros R I Sch x r1 r2 (Hrefl&_&_&Hrun) Hr. unfold step. cbn [xs rs].
  destruct (phase x); [| |split; [reflexivity|exact Hr]];
    (destruct (stop_due Sch x); [split; [reflexivity|exact Hr]|]);
    (destruct (foreign_due I x); [split; [reflexivity|exact Hr]|]);
    (destruct (cut_due Sch x); [split; [reflexivity|exact Hr]|]);
    (destruct (queue x) as [|t rest];
     [destruct (at_boundary I Sch x); (split; [reflexivity|exact Hr])|]);
    rewrite !arrival_run_head_unfold;
    destruct (arrival_interp_rel (requiv R) I _ _ (Hrun r1 r2 t Hr)
               (arrival_pre (set_progress (set_queue x rest) (S (progress x))) t)) as [E Q];
    destruct (interp I _ (run_task R r1 t)), (interp I _ (run_task R r2 t));
    cbn in E, Q |- *; subst; (split; [reflexivity|exact Q]).
Qed.

Lemma arrival_srel_step : forall R I s1 s2, I1 R -> arrival_srel R s1 s2 ->
  arrival_srel R (step R I (arrival_sinf I) s1) (step R I (arrival_sinf I) s2).
Proof.
  intros R I [x1 r1] [x2 r2] HI [Hx Hr]. cbn [xs rs] in Hx, Hr.
  rewrite (arrival_strip_eq x1 x2 Hx).
  destruct (arrival_step_micro R I x2 (micro x1) r1) as [M1 M2].
  destruct (arrival_step_rel R I (arrival_sinf I) x2 r1 r2 HI Hr) as [E Q].
  split; [rewrite M1, E; reflexivity|rewrite M2; exact Q].
Qed.

Lemma arrival_srel_refl : forall R s, I1 R -> arrival_srel R s s.
Proof. intros R s (H&_). split; [reflexivity|apply H]. Qed.

(** ** A step under any schedule *)

Lemma arrival_at_boundary_sinf : forall I Sch x, valid_schedule I Sch ->
  at_boundary I Sch x = None \/ at_boundary I Sch x = at_boundary I (arrival_sinf I) x.
Proof.
  intros I Sch x [_ Hv]. unfold at_boundary.
  destruct (phase x); [|right; reflexivity|right; reflexivity].
  destruct (held x), (waiter x) as [[[f tok] op]|]; try (right; reflexivity);
    (destruct (sub x) as [sb|]; [|right; reflexivity]); unfold at_boundary_sub;
    cbn [arrival_sinf arrived];
    (destruct (arrived Sch (micro x) <=? cursor x)%nat eqn:E; [left; reflexivity|]);
    right; specialize (Hv (micro x)); apply Nat.leb_gt in E;
    (replace (length (entries I) <=? cursor x)%nat with false
       by (symmetry; apply Nat.leb_gt; lia)); reflexivity.
Qed.

Lemma arrival_step_cases : forall R I Sch s, valid_schedule I Sch ->
  stop_due Sch (xs s) = true \/
  (exists k, cut_due Sch (xs s) = Some k /\
     step R I Sch s = {| xs := set_micro (on_cut (xs s) k) (S (micro (xs s)));
                         rs := rs s |}) \/
  step R I Sch s = arrival_bump s \/
  step R I Sch s = step R I (arrival_sinf I) s.
Proof.
  intros R I Sch [x r] Hv. cbn [xs rs]. unfold step. cbn [xs rs].
  destruct (phase x); [| |right; right; right; reflexivity];
    (destruct (stop_due Sch x) eqn:Hs; [left; reflexivity|]);
    cbn [stop_due cut_due arrival_sinf stop_at cut_at];
    (destruct (foreign_due I x); [right; right; right; reflexivity|]);
    (destruct (cut_due Sch x) as [k|] eqn:Hc;
     [right; left; exists k; split; reflexivity|]);
    (destruct (queue x); [|right; right; right; reflexivity]);
    (destruct (arrival_at_boundary_sinf I Sch x Hv) as [E|E]; rewrite E;
     [right; right; left; reflexivity|right; right; right; reflexivity]).
Qed.

(** ** The run under [arrival_sinf] *)

(** No cut in the trace, and no closing after a cut. *)
Definition arrival_good (x : XState) : Prop :=
  some_cut (phase x) = false /\ forallb arrival_ok (trace x) = true.

Lemma arrival_iterate_S : forall R I Sch n s,
  iterate R I Sch (S n) s = step R I Sch (iterate R I Sch n s).
Proof.
  intros R I Sch n. induction n as [|n IH]; intros s; [reflexivity|].
  change (iterate R I Sch (S (S n)) s) with (iterate R I Sch (S n) (step R I Sch s)).
  rewrite IH. reflexivity.
Qed.

Lemma arrival_good_step : forall R I s, arrival_good (xs s) ->
  arrival_good (xs (step R I (arrival_sinf I) s)).
Proof.
  intros R I s [G1 G2].
  destruct (arrival_step_grow R I (arrival_sinf I) s) as [_ H].
  destruct (H eq_refl eq_refl) as ((l&E&O&_)&_&C&_). split.
  - destruct (some_cut (phase (xs (step R I (arrival_sinf I) s)))) eqn:Hc; [|reflexivity].
    rewrite (C eq_refl eq_refl) in Hc. congruence.
  - rewrite E, forallb_app, G2, (O eq_refl). reflexivity.
Qed.

Lemma arrival_good_iterate : forall R I k s, arrival_good (xs s) ->
  arrival_good (xs (iterate R I (arrival_sinf I) k s)).
Proof.
  intros R I k. induction k as [|k IH]; intros s H; [exact H|].
  cbn [iterate]. apply IH. apply arrival_good_step. exact H.
Qed.

Lemma arrival_iterate_grow : forall R I k k' s, (k <= k')%nat ->
  prefix (trace (xs (iterate R I (arrival_sinf I) k s)))
         (trace (xs (iterate R I (arrival_sinf I) k' s))).
Proof.
  intros R I k k' s Hk. induction Hk as [|k' Hk IH]; [exists []; rewrite app_nil_r; reflexivity|].
  rewrite arrival_iterate_S.
  destruct (arrival_step_grow R I (arrival_sinf I) (iterate R I (arrival_sinf I) k' s))
    as [((l&E&_)&_) _].
  destruct IH as [m IH]. exists (m ++ l). rewrite E, IH, app_assoc. reflexivity.
Qed.

Definition arrival_x0 : XState :=
  mk POpen [] None None None false 0 0 0 0 [] None false [] 0 0 None.

Lemma arrival_good_initial : forall R p I r, arrival_good (xs (start_from R p I r)).
Proof.
  intros. cbn [start_from initial xs].
  destruct (arrival_issue_ext I arrival_x0 KSample None (fun c => SSample c FInitial))
    as ((l&E&O&_)&_&C&_). split.
  - unfold issue_sample. fold arrival_x0.
    destruct (some_cut (phase (issue I arrival_x0 KSample None (fun c => SSample c FInitial))))
      eqn:Hc; [|reflexivity].
    rewrite (C eq_refl) in Hc. discriminate.
  - unfold issue_sample. fold arrival_x0. rewrite E. exact O.
Qed.

Lemma arrival_nc_initial : forall R p I r, arrival_nc (xs (start_from R p I r)).
Proof.
  intros. cbn [start_from initial xs]. unfold issue_sample. fold arrival_x0.
  destruct (arrival_issue_ext I arrival_x0 KSample None (fun c => SSample c FInitial))
    as (_&_&_&N&_). apply N. split; [exact Logic.I|reflexivity].
Qed.

(** ** Cuts *)

Lemma arrival_before_cut_ok : forall t, forallb arrival_ok t = true -> before_cut t = t.
Proof.
  induction t as [|a t IH]; intros H; [reflexivity|].
  cbn in H. apply andb_true_iff in H as [H1 H2].
  destruct a; try discriminate; cbn; rewrite IH; auto.
Qed.

Lemma arrival_before_cut_app : forall t l, (exists c, In (ACut c) t) ->
  before_cut (t ++ l) = before_cut t.
Proof.
  induction t as [|a t IH]; intros l [c Hc]; [destruct Hc|].
  destruct Hc as [E|Hc]; [subst a; reflexivity|].
  destruct a; cbn; try reflexivity; f_equal; apply IH; exists c; exact Hc.
Qed.

Lemma arrival_before_cut_at : forall t c l, forallb arrival_ok t = true ->
  before_cut (t ++ ACut c :: l) = t.
Proof.
  induction t as [|a t IH]; intros c l H; [reflexivity|].
  cbn in H. apply andb_true_iff in H as [H1 H2].
  destruct a; try discriminate; cbn; rewrite IH; auto.
Qed.

Lemma arrival_stop_cut : forall Sch x, stop_due Sch x = true -> some_cut (phase x) = true.
Proof.
  intros Sch x H. unfold stop_due in H.
  destruct (stop_at Sch), (phase x) as [|[]|]; try discriminate; reflexivity.
Qed.

Lemma arrival_on_cut_closed : forall x k, phase (on_cut x k) <> POpen.
Proof.
  intros. destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf].
  unfold on_cut, close. destruct k, xp; try destruct cut; cbn; discriminate.
Qed.

Lemma arrival_srel_fields : forall R s1 s2, arrival_srel R s1 s2 ->
  trace (xs s1) = trace (xs s2) /\ phase (xs s1) = phase (xs s2) /\
  cursor (xs s1) = cursor (xs s2) /\ progress (xs s1) = progress (xs s2) /\
  next_cmd (xs s1) = next_cmd (xs s2).
Proof.
  intros R s1 s2 [H _].
  repeat split;
    [apply (f_equal trace) in H|apply (f_equal phase) in H|apply (f_equal cursor) in H
    |apply (f_equal progress) in H|apply (f_equal next_cmd) in H]; exact H.
Qed.

(** ** Following the run under [arrival_sinf] *)

(** After [n] steps under [Sch], a run is either related to the run under [arrival_sinf]
    after [k] steps, or has been cut, with its trace up to the cut equal to that run's trace
    after [k] steps, its cursor and progress count at least that run's, and its phase no
    longer open. *)
Definition arrival_follows (R : Runtime) (I : Inputs) (Sch : Schedule) (t0 s0 : Sys R)
    (n k : nat) : Prop :=
  let s := iterate R I Sch n s0 in
  let u := iterate R I (arrival_sinf I) k t0 in
  arrival_srel R s u \/
  ((exists c, In (ACut c) (trace (xs s))) /\ before_cut (trace (xs s)) = trace (xs u) /\
   (cursor (xs u) <= cursor (xs s))%nat /\ (progress (xs u) <= progress (xs s))%nat /\
   phase (xs s) <> POpen).

Lemma arrival_follow : forall R I Sch t0 s0, I1 R -> valid_schedule I Sch ->
  arrival_good (xs t0) -> arrival_srel R s0 t0 ->
  forall n, exists k, arrival_follows R I Sch t0 s0 n k.
Proof.
  intros R I Sch t0 s0 HI Hv Hg H0 n. induction n as [|n [k IH]].
  - exists 0%nat. left. exact H0.
  - unfold arrival_follows in *. rewrite arrival_iterate_S.
    set (s := iterate R I Sch n s0) in *.
    set (u := iterate R I (arrival_sinf I) k t0) in *.
    destruct IH as [IH|(Hc&Hb&Hu&Hp&Ho)].
    + pose proof (arrival_good_iterate R I k t0 Hg) as [G1 G2]. fold u in G1, G2.
      destruct (arrival_srel_fields R s u IH) as (Et&Ep&Ec&Epr&_).
      destruct (arrival_step_cases R I Sch s Hv) as [Hs|[(c&_&Hcut)|[Hw|He]]].
      * apply arrival_stop_cut in Hs. congruence.
      * exists k. right. fold u. rewrite Hcut. cbn [xs].
        destruct (arrival_on_cut_fields (xs s) c) as (E&_&U&G&_).
        rewrite arrival_trace_set_micro, E. split; [exists c; apply in_app_iff; right; left;
          reflexivity|].
        rewrite <- Et in G2. split; [rewrite arrival_before_cut_at; [exact Et|exact G2]|].
        rewrite arrival_cursor_set_micro, arrival_progress_set_micro,
          arrival_phase_set_micro. split; [lia|]. split; [lia|].
        apply arrival_on_cut_closed.
      * exists k. left. rewrite Hw. destruct IH as [IH1 IH2]. split; [|exact IH2].
        exact IH1.
      * exists (S k). left. rewrite He, arrival_iterate_S. fold u.
        apply arrival_srel_step; assumption.
    + exists k. right. fold u.
      destruct (arrival_step_grow R I Sch s) as [((l&E&_&_)&P&_&_&U&G) _].
      rewrite E. split; [destruct Hc as [c Hc]; exists c; apply in_app_iff; left; exact Hc|].
      split; [rewrite arrival_before_cut_app; assumption|].
      split; [lia|]. split; [lia|].
      intros Hq. rewrite Hq in P. destruct (phase (xs s)); cbn in P; congruence || lia.
Qed.
