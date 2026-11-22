(** * S2: replay.

    Up to its cut, the original attempt's trace [T] is the trace of the run under
    [arrival_sinf] after [k] steps (ArrivalSim.v). The replay's run under [arrival_sinf]
    takes the same steps as long as that run does: each of those steps reads a foreign input
    at a progress count the original reached, an entry the original consumed, and persisted
    commands that are the original's own. Where the original's run waits for good, or after
    [k] steps, its trace is [T], and from there the replay's run can only add to [T]; it
    issues no command at an index the replay has persisted, so it reports no mismatch. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Statements ArrivalBase ArrivalMicro ArrivalExt
  ArrivalGrow ArrivalSim ArrivalSwap ArrivalSwapStep ArrivalReplayLemmas Arrival.
Import ListNotations.
Open Scope Z_scope.

(** [I] with nothing persisted. *)
Definition arrival_fresh (I : Inputs) : Inputs :=
  {| entries := entries I; persisted := []; foreign := foreign I; stream := stream I;
     seed := seed I |}.

(** Past the point where it agrees with [T], the replay's run under [arrival_sinf] only
    adds to [T] and reports no mismatch. *)
Lemma arrival_beyond_step : forall R I' T u', persisted I' = commands T ->
  arrival_nc (xs u') -> prefix T (trace (xs u')) -> ~ In (AExit VMismatch) (trace (xs u')) ->
  let v := step R I' (arrival_sinf I') u' in
  arrival_nc (xs v) /\ prefix T (trace (xs v)) /\ ~ In (AExit VMismatch) (trace (xs v)).
Proof.
  intros R I' T u' Hp Hn Hpre Hm. cbn zeta.
  set (I0 := arrival_fresh I').
  destruct (arrival_step_grow R I0 (arrival_sinf I0) u') as [_ G].
  destruct (G eq_refl eq_refl) as ((l&E&_&M)&_&_&N&_).
  assert (Hm0 : ~ In (AExit VMismatch) (trace (xs (step R I0 (arrival_sinf I0) u')))).
  { rewrite E. intros H. apply in_app_iff in H as [H|H]; [exact (Hm H)|].
    assert (Hx : existsb arrival_mm l = true)
      by (apply existsb_exists; exists (AExit VMismatch); split; auto).
    destruct (M Hx) as [_ H0]. apply H0. reflexivity. }
  assert (Hpre0 : prefix T (trace (xs (step R I0 (arrival_sinf I0) u'))))
    by (rewrite E; eapply arrival_prefix_trans; [exact Hpre|exists l; reflexivity]).
  assert (Hn0 : arrival_nc (xs (step R I0 (arrival_sinf I0) u'))) by (apply N; exact Hn).
  destruct (arrival_step_swap R I0 I' u' eq_refl eq_refl) as [S1 _].
  - split; [exact Hm0|]. eapply arrival_agree_nc; [exact Hn0|right; exact Hpre0|exact Hp].
  - rewrite (S1 eq_refl). auto.
Qed.

Lemma arrival_two_runs : forall R I I' t0 t0' k C P, I1 R ->
  arrival_srel R t0 t0' -> arrival_nc (xs t0) -> arrival_nc (xs t0') ->
  let u := fun j => iterate R I (arrival_sinf I) j t0 in
  let u' := fun j => iterate R I' (arrival_sinf I') j t0' in
  let T := trace (xs (u k)) in
  ~ In (AExit VMismatch) T -> persisted I' = commands T -> stream I' = stream I ->
  (cursor (xs (u k)) <= C)%nat ->
  (forall i e, (i < C)%nat -> nth_error (entries I) i = Some e ->
     nth_error (entries I') i = Some e) ->
  (progress (xs (u k)) <= P)%nat -> (forall i, (i <= P)%nat -> foreign I' i = foreign I i) ->
  forall j, ((j <= k)%nat /\ arrival_srel R (u j) (u' j)) \/
            (prefix T (trace (xs (u' j))) /\ ~ In (AExit VMismatch) (trace (xs (u' j)))).
Proof.
  intros R I I' t0 t0' k C P HI H0 Hn0 Hn0' u u' T Hm Hp Hst Hc He Hpr Hf j.
  assert (Beyond : forall j, prefix T (trace (xs (u' j))) ->
            ~ In (AExit VMismatch) (trace (xs (u' j))) ->
            prefix T (trace (xs (u' (S j)))) /\
            ~ In (AExit VMismatch) (trace (xs (u' (S j))))).
  { intros j' Hpre Hm'. subst u'. cbn beta. rewrite arrival_iterate_S.
    destruct (arrival_beyond_step R I' T _ Hp (arrival_iterate_nc R I' _ j' t0' Hn0')
                Hpre Hm') as (_&A&B). auto. }
  induction j as [|j [[Hj IH]|[Hpre Hm']]].
  - left. split; [lia|exact H0].
  - destruct (arrival_srel_fields R _ _ IH) as (Et&_&Ec&Epr&_).
    assert (AtT : trace (xs (u j)) = T -> prefix T (trace (xs (u' (S j)))) /\
                  ~ In (AExit VMismatch) (trace (xs (u' (S j))))).
    { intros Eq. apply Beyond; rewrite <- Et, Eq;
        [exists []; rewrite app_nil_r; reflexivity|exact Hm]. }
    destruct (Nat.eq_dec j k) as [->|Hjk]; [right; apply AtT; reflexivity|].
    assert (Hj1 : (S j <= k)%nat) by lia.
    (* The original's next step, and what the replay's inputs give from the same state. *)
    assert (Hu1 : u (S j) = step R I (arrival_sinf I) (u j))
      by (subst u; cbn beta; apply arrival_iterate_S).
    assert (Hu1' : u' (S j) = step R I' (arrival_sinf I') (u' j))
      by (subst u'; cbn beta; apply arrival_iterate_S).
    destruct (arrival_iterate_grow R I (S j) k t0 Hj1) as [r Er]. fold (u (S j)) in Er.
    fold (u k) T in Er.
    assert (Hsafe : arrival_safe I' (trace (xs (step R I (arrival_sinf I) (u j))))).
    { rewrite <- Hu1. split.
      - intros H. apply Hm. rewrite Er. apply in_or_app. left. exact H.
      - eapply arrival_agree_nc; [|left; exists r; exact Er|exact Hp].
        subst u. apply arrival_iterate_nc. exact Hn0. }
    destruct (arrival_iterate_mono R I j k t0 Hj) as [_ Mp].
    fold (u j) (u k) in Mp.
    destruct (arrival_step_swap R I I' (u j) Hst (Hf _ (Nat.le_trans _ _ _ Mp Hpr)) Hsafe)
      as [P1 P2].
    assert (Next : step R I' (arrival_sinf I') (u j) = step R I (arrival_sinf I) (u j) ->
                   (S j <= k)%nat /\ arrival_srel R (u (S j)) (u' (S j))).
    { intros Eq. split; [exact Hj1|]. rewrite Hu1, Hu1', <- Eq.
      apply arrival_srel_step; assumption. }
    destruct (arrival_step_cursor R I (u j)) as [Ecur|[Ecur [e Ee]]].
    + destruct (P2 Ecur) as [Stuck|Eq]; [|left; apply Next; exact Eq].
      right. apply AtT. pose proof (arrival_stuck R I (u j) HI Stuck (k - j)) as Hs.
      assert (Euk : u k = iterate R I (arrival_sinf I) (k - j) (u j)).
      { subst u. cbn beta. rewrite <- arrival_iterate_add. f_equal. lia. }
      rewrite <- Euk in Hs.
      destruct (arrival_srel_fields R _ _ Hs) as (Et'&_). exact (eq_sym Et').
    + left. apply Next. apply P1.
      destruct (arrival_iterate_mono R I (S j) k t0 Hj1) as [Mc _].
      fold (u (S j)) (u k) in Mc. rewrite <- Hu1 in Ecur.
      rewrite Ee. apply (He _ e); [lia|exact Ee].
  - right. apply Beyond; assumption.
Qed.

(** The original attempt up to its cut is the run under [arrival_sinf] after some [k]
    steps, which has consumed no more and made no more progress than the original. *)
Lemma arrival_original : forall R I Sch t0 n, I1 R -> valid_schedule I Sch ->
  arrival_good (xs t0) ->
  let x := xs (iterate R I Sch n t0) in
  exists k, let u := xs (iterate R I (arrival_sinf I) k t0) in
    before_cut (trace x) = trace u /\ (cursor u <= cursor x)%nat /\
    (progress u <= progress x)%nat.
Proof.
  intros R I Sch t0 n HI Hv Hg x.
  destruct (arrival_follow R I Sch t0 t0 HI Hv Hg (arrival_srel_refl R t0 HI) n)
    as [k [H|(_&Hb&Hc&Hp&_)]]; exists k; cbn zeta; [|auto].
  destruct (arrival_srel_fields R _ _ H) as (Et&_&Ec&Ep&_). fold x in Et, Ec, Ep.
  rewrite Et, Ec, Ep. split; [|split; lia].
  apply arrival_before_cut_ok. apply (arrival_good_iterate R I k t0 Hg).
Qed.

Lemma arrival_firstn_entry : forall (l more : list JIn) C i e, (i < C)%nat ->
  nth_error l i = Some e -> nth_error (firstn C l ++ more) i = Some e.
Proof.
  intros l more C i e Hi H.
  assert (Hl : (i < length l)%nat) by (apply nth_error_Some; congruence).
  rewrite nth_error_app1; [|rewrite length_firstn; lia].
  rewrite nth_error_firstn. destruct (i <? C)%nat eqn:E; [exact H|].
  apply Nat.ltb_ge in E. lia.
Qed.

Theorem arrival_s2 : S2.
Proof.
  intros R HM p I Sch n I' Sch' n' more r' Hr' Hv Hv' x Hnm Hpers Hent Hfor Hst Hseed t'.
  pose proof HM as [HI _]. pose proof HI as (Hrefl&Hsym&_).
  set (t0 := initial R p I) in x.
  assert (Hg : arrival_good (xs t0)) by apply (arrival_good_initial R p I (init R p (seed I))).
  destruct (arrival_original R I Sch t0 n HI Hv Hg) as [k (Hb&Hc&Hp)]. fold x in Hb, Hc, Hp.
  set (T := trace (xs (iterate R I (arrival_sinf I) k t0))) in *.
  assert (HmT : ~ In (AExit VMismatch) T).
  { intros H. apply Hnm. rewrite <- Hb in H. eapply arrival_prefix_in; [|exact H].
    apply arrival_before_cut_prefix. }
  rewrite Hb in Hpers |- *.
  set (t0' := start_from R p I' r').
  assert (Hn0 : arrival_nc (xs t0)) by apply (arrival_nc_initial R p I (init R p (seed I))).
  assert (Hn0' : arrival_nc (xs t0')) by apply arrival_nc_initial.
  (* The two attempts start in the same executor state. *)
  assert (H0 : arrival_srel R t0 t0').
  { split.
    - cbn [t0 t0' initial start_from xs]. unfold issue_sample. f_equal. symmetry.
      apply arrival_issue_swap.
      destruct (arrival_iterate_grow R I 0 k t0 (Nat.le_0_l k)) as [r E]. fold T in E.
      split.
      + intros H. apply HmT. rewrite E. apply in_or_app. left. exact H.
      + eapply arrival_agree_nc; [exact Hn0|left; exists r; exact E|exact Hpers].
    - cbn [t0 t0' initial start_from rs]. rewrite <- Hseed. apply Hsym. exact Hr'. }
  pose proof (arrival_two_runs R I I' t0 t0' k (cursor x) (progress x) HI H0 Hn0 Hn0'
    HmT Hpers Hst Hc) as Two.
  cbn zeta in Two. fold T in Two.
  assert (Hrun : forall j, compatible T (trace (xs (iterate R I' (arrival_sinf I') j t0'))) /\
                   ~ In (AExit VMismatch) (trace (xs (iterate R I' (arrival_sinf I') j t0')))).
  { intros j.
    destruct (Two (fun i e Hi He => eq_ind_r (fun l => nth_error l i = Some e)
                     (arrival_firstn_entry (entries I) more (cursor x) i e Hi He) Hent)
                  Hp Hfor j) as [[Hj Hs]|[Hpre Hm]].
    - destruct (arrival_srel_fields R _ _ Hs) as (Et&_). rewrite <- Et.
      destruct (arrival_iterate_grow R I j k t0 Hj) as [r E]. fold T in E.
      split; [right; exists r; exact E|].
      intros H. apply HmT. rewrite E. apply in_or_app. left. exact H.
    - split; [left; exact Hpre|exact Hm]. }
  assert (Hg' : arrival_good (xs t0')) by apply arrival_good_initial.
  destruct (arrival_before_cut_follow R I' Sch' t0' t0' n' HI Hv' Hg'
              (arrival_srel_refl R t0' HI)) as [k' E'].
  unfold t', run_from. fold t0'. rewrite E'.
  destruct (Hrun k') as [C M]. split; [|exact C].
  intros H. apply M. rewrite <- E'.
  destruct (arrival_mm_before_cut R I' Sch' t0' Hv' (proj2 Hg') n') as [_ B].
  apply B. exact H.
Qed.
