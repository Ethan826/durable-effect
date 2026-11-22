(** * S1, S3 and S10: arrival independence, violations at the same position, and draws.

    Up to its cut, a run's trace is the trace of the run under [arrival_sinf] after some
    number of steps (ArrivalSim.v), and that run's traces only grow. Two runs from
    equivalent runtime states follow the same such run, so their traces up to their cuts
    are prefixes of one sequence. S3 and S10 read this off positions and draws. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Statements ArrivalBase ArrivalExt ArrivalGrow
  ArrivalSim.
Import ListNotations.
Open Scope Z_scope.

Lemma arrival_before_cut_follow : forall R I Sch t0 s0 n, I1 R -> valid_schedule I Sch ->
  arrival_good (xs t0) -> arrival_srel R s0 t0 ->
  exists k, before_cut (trace (xs (iterate R I Sch n s0))) =
            trace (xs (iterate R I (arrival_sinf I) k t0)).
Proof.
  intros R I Sch t0 s0 n HI Hv Hg H0.
  destruct (arrival_follow R I Sch t0 s0 HI Hv Hg H0 n) as [k [H|(_&H&_)]];
    exists k; [|exact H].
  destruct (arrival_srel_fields R _ _ H) as (E&_). rewrite E.
  apply arrival_before_cut_ok. apply (arrival_good_iterate R I k t0 Hg).
Qed.

Lemma arrival_start_srel : forall R p I r1 r2, I1 R ->
  requiv R r1 (init R p (seed I)) -> requiv R r2 (init R p (seed I)) ->
  arrival_srel R (start_from R p I r2) (start_from R p I r1).
Proof.
  intros R p I r1 r2 (_&Hsym&Htrans&_) H1 H2. split; [reflexivity|].
  cbn [start_from rs]. eapply Htrans; [exact H2|apply Hsym; exact H1].
Qed.

Lemma arrival_compatible_ideal : forall R I t0 k1 k2,
  compatible (trace (xs (iterate R I (arrival_sinf I) k1 t0)))
             (trace (xs (iterate R I (arrival_sinf I) k2 t0))).
Proof.
  intros. destruct (Nat.le_ge_cases k1 k2); [left|right];
    apply arrival_iterate_grow; assumption.
Qed.

Theorem arrival_s1 : S1.
Proof.
  intros R HM p I Sch1 Sch2 r1 r2 n1 n2 Hv1 Hv2 Hr1 Hr2.
  destruct HM as [HI _]. unfold run_from.
  set (t0 := start_from R p I r1).
  assert (Hg : arrival_good (xs t0)) by apply arrival_good_initial.
  destruct (arrival_before_cut_follow R I Sch1 t0 t0 n1 HI Hv1 Hg
              (arrival_srel_refl R t0 HI)) as [k1 E1].
  destruct (arrival_before_cut_follow R I Sch2 t0 (start_from R p I r2) n2 HI Hv2 Hg
              (arrival_start_srel R p I r1 r2 HI Hr1 Hr2)) as [k2 E2].
  rewrite E1, E2. apply arrival_compatible_ideal.
Qed.

Lemma arrival_run_from_init : forall R p I Sch n,
  run R p I Sch n = run_from R p I Sch (init R p (seed I)) n.
Proof. reflexivity. Qed.

Lemma arrival_nth_compatible : forall {X} (t1 t2 : list X) i v,
  compatible t1 t2 -> nth_error t1 i = Some v -> (i < length t2)%nat ->
  nth_error t2 i = Some v.
Proof.
  intros X t1 t2 i v [[r E]|[r E]] H Hl; subst.
  - rewrite nth_error_app1; [exact H|]. apply nth_error_Some. congruence.
  - rewrite nth_error_app1 in H; assumption.
Qed.

Theorem arrival_s3 : S3.
Proof.
  intros R HM p I Sch1 Sch2 n1 n2 i v Hv1 Hv2 t1 t2 H Hl.
  pose proof HM as ((Hrefl&_)&_).
  assert (C : compatible t1 t2).
  { subst t1 t2. rewrite !arrival_run_from_init.
    apply (arrival_s1 R HM p I Sch1 Sch2); auto. }
  eapply arrival_nth_compatible; eassumption.
Qed.

Lemma arrival_draws_app : forall f a b, draws_of f (a ++ b) = draws_of f a ++ draws_of f b.
Proof. intros. unfold draws_of. apply flat_map_app. Qed.

Theorem arrival_s10 : S10.
Proof.
  intros R HM p I Sch1 Sch2 r1 r2 n1 n2 f Hv1 Hv2 Hr1 Hr2.
  destruct (arrival_s1 R HM p I Sch1 Sch2 r1 r2 n1 n2 Hv1 Hv2 Hr1 Hr2) as [[r E]|[r E]];
    [left|right]; exists (draws_of f r); rewrite E; apply arrival_draws_app.
Qed.
