(** * S9, single-fiber equivalence.

    Every state revision 4 reaches from a single-fiber program keeps the invariant [SF] of
    SingleFiberLemmas.v. From such a state, a step of revision 4 and a step of revision 3 give
    the same state, unless revision 4's step starts a sleep chain or records
    [BlockedWithNothingAwaited]. [in_common] rules out the first at every step, and the second
    stays in the trace once recorded, so both executors take the same steps up to [n]. *)

From Coq Require Import List ZArith Bool Arith Lia.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model Executor Statements SingleStepLemmas SingleStepInvariants
  ExecutorLemmas SingleFiberLemmas.
Import ListNotations.
Open Scope Z_scope.

(** ** The invariant across a micro-step *)

Lemma tick_SF : forall st b, SF st -> SF (tick st b).
Proof. intros st b H. exact H. Qed.

Lemma finish_SF : forall st e, SF (finish st e).
Proof. intros st e H. discriminate H. Qed.

Lemma violate_SF : forall st v, SF (violate st v).
Proof. intros st v. apply finish_SF. Qed.

Lemma end_attempt_SF : forall st how, SF (end_attempt st how).
Proof. intros st [|]; apply finish_SF. Qed.

(** The one fiber resumed after a delivery. *)
Lemma resume_SF : forall st g o,
  fibers st = [g] -> fiber_ok g -> SF (resume st 0 o).
Proof.
  intros st g o Hfs Hg. pose proof Hg as (Hh & Hc & Hfn & Hp). unfold resume.
  rewrite Hfs, find_one by exact Hh.
  apply SF_intro with (set_code g (match pending g, o with
                                   | ResumeOutcome k, Some v => k v
                                   | ResumeUnit k, _ => k tt
                                   | _, _ => code g
                                   end) NoPending Ready);
    [|apply fiber_ok_set; [exact Hg|]|exact I].
  - cbn [fibers update]. apply put_one. reflexivity.
  - destruct (pending g); [exact Hc| |apply Hp|exact Hc]; destruct o; [apply Hp|exact Hc].
Qed.

(** A cancellation delivered to the one fiber. *)
Lemma cancel_SF : forall st g op,
  fibers st = [g] -> fiber_ok g -> SF (cancel st op 0).
Proof.
  intros st g op Hfs Hg. unfold cancel.
  match goal with
  | |- SF (interrupt_fiber ?s 0) =>
      destruct (interrupt_one s g 0 Hfs Hg eq_refl) as (y & Hy & Hyok & Hya)
  end.
  apply SF_intro with y; [exact Hy | exact Hyok | rewrite Hya; exact I].
Qed.

Lemma deliver_SF : forall E st aw,
  SF st -> finished st = None -> awaited st = Some aw -> SF (deliver E st aw).
Proof.
  intros E st aw H Hf Ha. destruct (H Hf) as (g & Hfs & Hg & Haw).
  rewrite Ha in Haw. destruct Haw as [Hh Hs].
  destruct aw as [h op|h op c r]; cbn in Hh; subst h; unfold deliver.
  - destruct (cancelled_at E op); [apply cancel_SF with g|apply resume_SF with g]; assumption.
  - destruct (cancelled_at E op); [apply cancel_SF with g; assumption|].
    destruct r as [|d|]; [apply resume_SF with g; assumption| |];
      [destruct (d <=? max_chunk)|];
      (apply SF_intro with g; [exact Hfs | exact Hg | split; [reflexivity | exact Hs]]).
Qed.

(** The task at the head of the queue, under revision 4: the invariant holds after it, and
    revision 3 runs it the same way unless revision 4 starts a sleep chain. *)
Lemma run_head_one : forall P E st h rest,
  SF st -> finished st = None ->
  SF (run_head policy_v1 P E st h rest) /\
  (chain_free (run_head policy_v1 P E st h rest) ->
   run_head policy_v1 P E st h rest = run_head policy_rev3 P E st h rest).
Proof.
  intros P E st h rest H Hf. destruct (H Hf) as (g & Hfs & Hg & Haw).
  (* With the fuel abstracted, the kernel cannot unfold [run_fiber] while checking. *)
  unfold run_head. generalize max_ops as m. intros m. cbn [fibers update]. rewrite Hfs.
  assert (Hkept : SF (update st [g] rest (awaited st) (abandoned st) (next_op st)
    (next_sample st) (next_handle st) (draws st) (logical st) (trace st) (finished st)))
    by (apply SF_intro with g; [reflexivity | exact Hg | exact Haw]).
  destruct (find_fiber h [g]) as [f|] eqn:Hfind; [|split; [exact Hkept | reflexivity]].
  apply find_one_inv in Hfind. destruct Hfind as [-> _].
  destruct (status g) eqn:Hs; try (split; [exact Hkept | reflexivity]).
  assert (Ha : awaited st = None)
    by (destruct (awaited st); [destruct Haw; contradiction | reflexivity]).
  destruct Hg as (Hh & Hrest).
  destruct (run_fiber_one P E m m
              (update st [g] rest (awaited st) (abandoned st) (next_op st) (next_sample st)
                 (next_handle st) (draws st) (logical st) (trace st) (finished st)) g g
              eq_refl Hh (conj Hh Hrest) Ha) as [H1 H2].
  split; [apply tick_SF; exact H1|]. intros Hc. f_equal. apply H2. exact Hc.
Qed.

Lemma violate_in : forall st v, In (Violated v) (trace (violate st v)).
Proof.
  intros st v. cbn. apply in_or_app. left. apply in_or_app. right. left. reflexivity.
Qed.

(** One micro-step of revision 4 keeps the invariant, and it is revision 3's step unless it
    starts a sleep chain or records [BlockedWithNothingAwaited]. *)
Lemma turn_one : forall P E A st,
  SF st -> finished st = None ->
  SF (turn policy_v1 P E A st) /\
  (chain_free (turn policy_v1 P E A st) ->
   ~ In (Violated BlockedWithNothingAwaited) (trace (turn policy_v1 P E A st)) ->
   turn policy_v1 P E A st = turn policy_rev3 P E A st).
Proof.
  intros P E A st H Hf. unfold turn.
  destruct (queue st) as [|h rest].
  2: { destruct (run_head_one P E st h rest H Hf) as [H1 H2].
       split; [exact H1|]. intros Hc _. exact (H2 Hc). }
  destruct (awaited st) as [aw|] eqn:Ha.
  - destruct (A (awaited_op aw) (micro st)); (split; [|reflexivity]); apply tick_SF;
      [apply deliver_SF|]; assumption.
  - destruct (root_done st); [split; [apply tick_SF, finish_SF | reflexivity]|].
    cbn [blocked_is_violation policy_v1 policy_rev3].
    split; [apply tick_SF, violate_SF|]. intros _ Hn. exfalso. apply Hn. apply violate_in.
Qed.

Lemma step_one : forall P E A st,
  SF st ->
  SF (step policy_v1 P E A no_outside_resumes st) /\
  (chain_free (step policy_v1 P E A no_outside_resumes st) ->
   ~ In (Violated BlockedWithNothingAwaited)
       (trace (step policy_v1 P E A no_outside_resumes st)) ->
   step policy_v1 P E A no_outside_resumes st
     = step policy_rev3 P E A no_outside_resumes st).
Proof.
  intros P E A st H. destruct (finished st) as [e|] eqn:Hf.
  { rewrite !(step_finished _ _ _ _ _ _ e Hf). split; [exact H | reflexivity]. }
  rewrite !step_unfold by (exact Hf || reflexivity).
  destruct (ends_at E) as [[n how]|]; [destruct (Nat.eqb n (progress st))|];
    try (apply turn_one; assumption).
  split; [apply tick_SF, end_attempt_SF | reflexivity].
Qed.

Lemma initial_SF : forall P E, single_fiber P -> SF (initial P E).
Proof.
  intros P E [Hm Hf]. apply SF_intro with (new_fiber 0 (bodies P (root P)));
    [reflexivity | repeat split; assumption | exact I].
Qed.

Lemma reachable_SF : forall P E A k, single_fiber P ->
  SF (iterate policy_v1 P E A no_outside_resumes k (initial P E)).
Proof.
  intros P E A k Hs. induction k as [|k IH]; [apply initial_SF; exact Hs|].
  rewrite iterate_S. apply step_one. exact IH.
Qed.

(** ** S9 *)

Theorem s9 : S9.
Proof.
  intros P E A n Hs Hc Hn. unfold run, run_rev3. f_equal.
  enough (Hk : forall k, (k <= n)%nat ->
    iterate policy_v1 P E A no_outside_resumes k (initial P E)
      = iterate policy_rev3 P E A no_outside_resumes k (initial P E)) by (apply Hk; lia).
  intros k. induction k as [|k IH]; intros Hle; [reflexivity|].
  rewrite !iterate_S, <- IH by lia.
  apply step_one; [apply reachable_SF; exact Hs| |].
  - intros h op c r Ha. rewrite <- iterate_S in Ha. exact (Hc (S k) h op c r Ha).
  - intros Hin. apply Hn.
    destruct (iterate_prefix policy_v1 P E A no_outside_resumes (S k) n (initial P E) Hle)
      as [tail Ht].
    unfold run. rewrite Ht, iterate_S. apply in_or_app. left. exact Hin.
Qed.
