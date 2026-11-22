(** * S1, arrival independence, and S1_end.

    A run under any arrival schedule is the replay's run with waiting steps inserted: each
    step either takes the replay's step or waits, and waiting changes only the micro-step
    counter (ExecutorLemmas.v). The replay's traces only grow, so any two runs are prefixes of
    one sequence. The schedule's monotonicity is not needed. *)

From Coq Require Import List ZArith Bool Arith.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model Executor Statements ExecutorLemmas.
Import ListNotations.

(** The replay of environment [E] after [m] progress steps. *)
Definition replay (pol : Policy) (P : Program) (E : Env) (m : nat) : State :=
  Nat.iter m (step pol P E arrived no_outside_resumes) (initial P E).

Lemma replay_S : forall pol P E m,
  replay pol P E (S m) = step pol P E arrived no_outside_resumes (replay pol P E m).
Proof. reflexivity. Qed.

Lemma replay_prefix : forall pol P E m m', (m <= m')%nat ->
  prefix (trace (replay pol P E m)) (trace (replay pol P E m')).
Proof.
  intros pol P E m m' Hle. induction Hle as [|m' Hle IH]; [apply prefix_refl|].
  rewrite replay_S. eapply prefix_trans; [apply IH|apply step_prefix].
Qed.

Lemma replays_compatible : forall pol P E m m',
  compatible (trace (replay pol P E m)) (trace (replay pol P E m')).
Proof.
  intros pol P E m m'. destruct (Nat.le_ge_cases m m');
    [left|right]; apply replay_prefix; assumption.
Qed.

Lemma same_values_refl : forall E, same_values E E.
Proof. intros E. repeat split; reflexivity. Qed.

(** A step that the environment's ending does not interrupt. *)
Lemma step_not_ending : forall pol P E1 E2 A st j,
  same_values E1 E2 -> fires E1 st = fires E2 st -> finished st = None ->
  step pol P E1 A no_outside_resumes (set_micro st j)
    = set_micro (step pol P E2 arrived no_outside_resumes st) (S j) \/
  step pol P E1 A no_outside_resumes (set_micro st j) = set_micro st (S j).
Proof.
  intros pol P E1 E2 A st j Hv Hf Hn.
  destruct (step_cases pol P E1 A (set_micro st j)) as [H|H]; rewrite H.
  - left. apply step_set_micro; assumption.
  - right. rewrite tick_false. reflexivity.
Qed.

(** ** S1 *)

(** Under any arrival schedule, the run after [n] micro-steps is the replay after some number
    of progress steps, with a different counter. *)
Lemma stutter : forall pol P E1 E2 A n,
  same_values E1 E2 -> ends_at E1 = ends_at E2 ->
  exists m j,
    iterate pol P E1 A no_outside_resumes n (initial P E1) = set_micro (replay pol P E2 m) j.
Proof.
  intros pol P E1 E2 A n Hv He. pose proof Hv as (_ & Hs & _ & _).
  induction n as [|n (m & j & IH)].
  - exists 0%nat, 0%nat. cbn [iterate]. rewrite (initial_same P E1 E2 Hs).
    symmetry. apply set_micro_id.
  - rewrite iterate_S, IH.
    destruct (finished (replay pol P E2 m)) as [e|] eqn:Hn.
    + exists m, j. apply (step_finished _ _ _ _ _ _ e). exact Hn.
    + assert (Hf : fires E1 (replay pol P E2 m) = fires E2 (replay pol P E2 m))
        by (unfold fires; rewrite He; reflexivity).
      destruct (step_not_ending pol P E1 E2 A _ j Hv Hf Hn) as [H|H]; rewrite H.
      * exists (S m), (S j). reflexivity.
      * exists m, (S j). reflexivity.
Qed.

(** S1 without its hypothesis that the schedules are monotone: delivery happens only at turn
    boundaries (D5), so a schedule can delay a step and never reorder one. *)
Theorem s1_any_schedule : forall P E1 E2 A1 A2 n1 n2,
  same_values E1 E2 -> ends_at E1 = ends_at E2 ->
  compatible (run P E1 A1 n1) (run P E2 A2 n2).
Proof.
  intros P E1 E2 A1 A2 n1 n2 Hv He.
  destruct (stutter policy_v1 P E1 E2 A1 n1 Hv He) as (m1 & j1 & H1).
  destruct (stutter policy_v1 P E2 E2 A2 n2 (same_values_refl E2) eq_refl)
    as (m2 & j2 & H2).
  unfold run. rewrite H1, H2, !trace_set_micro. apply replays_compatible.
Qed.

Theorem s1 : S1.
Proof. intros P E1 E2 A1 A2 n1 n2 Hv He _. apply s1_any_schedule; assumption. Qed.

(** ** S1_end *)

Lemma step_ending : forall pol P E A st how,
  finished st = None -> fires E st = Some how ->
  step pol P E A no_outside_resumes st = tick (end_attempt st how) true.
Proof.
  intros pol P E A st how Hn Hf. unfold step. rewrite Hn.
  change (no_outside_resumes _) with (@None (nat * nat)). cbv iota.
  unfold fires in Hf. destruct (ends_at E) as [[n h]|]; [|discriminate].
  destruct (Nat.eqb n (progress st)); [|discriminate].
  injection Hf as <-. reflexivity.
Qed.

Lemma end_attempt_finished : forall st how, exists e, finished (end_attempt st how) = Some e.
Proof. intros st []; eexists; reflexivity. Qed.

Lemma interrupt_fiber_trace : forall st h,
  trace (interrupt_fiber st h) = trace st \/
  trace (interrupt_fiber st h) = trace st ++ [Interrupted h].
Proof.
  intros st h. unfold interrupt_fiber.
  destruct (find_fiber h (fibers st)) as [f|]; [|left; reflexivity].
  destruct (status f);
    try (destruct (awaited st) as [[h' op|h' op c r]|]; try destruct (Nat.eqb h' h));
    first [left; reflexivity | right; reflexivity].
Qed.

Lemma fold_interrupt_trace : forall fs st, exists hs,
  trace (fold_left (fun s f => interrupt_fiber s (handle f)) fs st)
  = trace st ++ map Interrupted hs.
Proof.
  induction fs as [|f fs IH]; intros st.
  - exists []. symmetry. apply app_nil_r.
  - simpl. destruct (IH (interrupt_fiber st (handle f))) as [hs ->].
    destruct (interrupt_fiber_trace st (handle f)) as [-> | ->].
    + exists hs. reflexivity.
    + exists (handle f :: hs). rewrite <- app_assoc. reflexivity.
Qed.

(** The attempt-end turn adds an ending and nothing else. *)
Lemma end_attempt_trace : forall st how, exists tail,
  trace (end_attempt st how) = trace st ++ tail /\ ending_tail tail.
Proof.
  intros st []; [|exists [Exited Crashed]; split; [reflexivity|right; reflexivity]].
  destruct (fold_interrupt_trace (filter (fun f => match status f with
      Done => false | _ => true end) (fibers st)) st) as [hs Hhs].
  exists (map Interrupted hs ++ [Exited Suspended]). split; [|left; exists hs; reflexivity].
  unfold end_attempt. cbn [trace finish emit update]. rewrite Hhs, app_assoc. reflexivity.
Qed.

(** Under an ending the other environment lacks, the run is the replay without an ending,
    up to the counter, until the ending's turn, and that turn's state afterwards. *)
Lemma stutter_end : forall pol P E1 E2 A n,
  same_values E1 E2 -> ends_at E2 = None ->
  (exists m j,
     iterate pol P E1 A no_outside_resumes n (initial P E1) = set_micro (replay pol P E2 m) j)
  \/
  (exists m j how,
     finished (replay pol P E2 m) = None /\
     iterate pol P E1 A no_outside_resumes n (initial P E1)
       = set_micro (tick (end_attempt (replay pol P E2 m) how) true) j).
Proof.
  intros pol P E1 E2 A n Hv He. pose proof Hv as (_ & Hs & _ & _).
  induction n as [|n [(m & j & IH)|(m & j & how & Hn & IH)]].
  - left. exists 0%nat, 0%nat. cbn [iterate]. rewrite (initial_same P E1 E2 Hs).
    symmetry. apply set_micro_id.
  - rewrite iterate_S, IH.
    destruct (finished (replay pol P E2 m)) as [e|] eqn:Hn.
    + left. exists m, j. apply (step_finished _ _ _ _ _ _ e). exact Hn.
    + destruct (fires E1 (replay pol P E2 m)) as [how|] eqn:Hf.
      * right. exists m, (S j), how. split; [exact Hn|].
        rewrite (step_ending _ _ _ _ (set_micro (replay pol P E2 m) j) how Hn Hf).
        rewrite end_attempt_set_micro, tick_set_micro.
        reflexivity.
      * assert (Hf2 : fires E1 (replay pol P E2 m) = fires E2 (replay pol P E2 m))
          by (rewrite Hf; unfold fires; rewrite He; reflexivity).
        left. destruct (step_not_ending pol P E1 E2 A _ j Hv Hf2 Hn) as [H|H]; rewrite H.
        -- exists (S m), (S j). reflexivity.
        -- exists m, (S j). reflexivity.
  - right. exists m, j, how. split; [exact Hn|]. rewrite iterate_S, IH.
    destruct (end_attempt_finished (replay pol P E2 m) how) as [e He'].
    apply (step_finished _ _ _ _ _ _ e). exact He'.
Qed.

Theorem s1_end : S1_end.
Proof.
  intros P E1 E2 A1 A2 n1 n2 Hv He _.
  destruct (stutter policy_v1 P E2 E2 A2 n2 (same_values_refl E2) eq_refl)
    as (m2 & j2 & H2).
  unfold run. rewrite H2, trace_set_micro.
  destruct (stutter_end policy_v1 P E1 E2 A1 n1 Hv He)
    as [(m1 & j1 & H1)|(m1 & j1 & how & _ & H1)]; rewrite H1, trace_set_micro.
  - exists (trace (replay policy_v1 P E2 m1)), []. split; [symmetry; apply app_nil_r|].
    split; [left; reflexivity|apply replays_compatible].
  - rewrite trace_tick.
    destruct (end_attempt_trace (replay policy_v1 P E2 m1) how) as (tail & Ht & Hend).
    exists (trace (replay policy_v1 P E2 m1)), tail.
    split; [exact Ht|]. split; [right; exact Hend|apply replays_compatible].
Qed.
