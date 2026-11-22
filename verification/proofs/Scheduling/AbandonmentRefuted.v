(** * S11 as written is refuted, and so is its strengthening to every step.

    The model records a delivered cancellation as an abandonment: [deliver] interrupts the
    awaiting fiber while the cancelled operation is still the awaited one, and
    [interrupt_fiber] then adds that operation to [abandoned]. The operation's cancellation
    was consumed, so changing whether it is cancelled changes the trace at the very step that
    put it in [abandoned]. Both theorems are closed by evaluation in the kernel. *)

From Coq Require Import List ZArith Bool Arith.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model Executor Statements.
Import ListNotations.
Open Scope nat_scope.

(** The root awaits one durable operation and finishes. *)
Definition one_await : Program :=
  {| bodies := fun _ => {| main := Vis (StartAwait 5 0) (fun _ => Ret tt);
                           finalizer := Ret tt |};
     root := 0 |}.

(** Operation 0 is cancelled. *)
Definition cancels_first : Env :=
  {| outcome_of := fun _ => Value 7;
     sample_of := fun n => {| true_time := (100 + Z.of_nat n)%Z; host_error := 0%Z |};
     cancelled_at := fun n => Nat.eqb n 0; random_of := fun n => n; ends_at := None |}.

(** The same environment, except that operation 0 completes. *)
Definition completes_first : Env :=
  {| outcome_of := fun _ => Value 7;
     sample_of := fun n => {| true_time := (100 + Z.of_nat n)%Z; host_error := 0%Z |};
     cancelled_at := fun _ => false; random_of := fun n => n; ends_at := None |}.

Definition all_arrived : Arrival := fun _ _ => true.

(** After two micro-steps operation 0 is in [abandoned], although it was delivered as a
    cancellation; the two traces differ at that step. *)
Lemma cancelled_counted_abandoned :
  abandoned (iterate policy_v1 one_await cancels_first all_arrived no_outside_resumes 2
               (initial one_await cancels_first)) = [0] /\
  run one_await cancels_first all_arrived 2 <> run one_await completes_first all_arrived 2.
Proof. vm_compute. split; [reflexivity | discriminate]. Qed.

(** The environments differ only in whether operation 0 is cancelled. *)
Lemma differ_only_at_first :
  (forall n, n <> 0 -> outcome_of cancels_first n = outcome_of completes_first n) /\
  (forall n, n <> 0 -> cancelled_at cancels_first n = cancelled_at completes_first n) /\
  (forall n, sample_of cancels_first n = sample_of completes_first n) /\
  (forall n, random_of cancels_first n = random_of completes_first n) /\
  ends_at cancels_first = ends_at completes_first.
Proof.
  repeat split; try reflexivity.
  intros [|n] Hn; [contradiction Hn; reflexivity | reflexivity].
Qed.

Theorem s11_refuted : ~ S11.
Proof.
  intros H. destruct differ_only_at_first as (Ho & Hc & Hs & Hr & He).
  destruct cancelled_counted_abandoned as [Ha Hne].
  apply Hne.
  refine (H one_await cancels_first completes_first all_arrived 2 0 _ Ho Hc Hs Hr He 2 _).
  - cbv zeta. rewrite Ha. left. reflexivity.
  - apply le_n.
Qed.

(** S11 with the bound on the step count removed: what the brief called [s11_all_steps]. *)
Definition S11_all_steps : Prop :=
  forall P E1 E2 A k op,
    let st := iterate policy_v1 P E1 A no_outside_resumes k (initial P E1) in
    In op (abandoned st) ->
    (forall n, n <> op -> outcome_of E1 n = outcome_of E2 n) ->
    (forall n, n <> op -> cancelled_at E1 n = cancelled_at E2 n) ->
    (forall n, sample_of E1 n = sample_of E2 n) ->
    (forall n, random_of E1 n = random_of E2 n) ->
    ends_at E1 = ends_at E2 ->
    forall n, run P E1 A n = run P E2 A n.

Theorem s11_all_steps_refuted : ~ S11_all_steps.
Proof.
  intros H. destruct differ_only_at_first as (Ho & Hc & Hs & Hr & He).
  destruct cancelled_counted_abandoned as [Ha Hne].
  apply Hne.
  refine (H one_await cancels_first completes_first all_arrived 2 0 _ Ho Hc Hs Hr He 2).
  cbv zeta. rewrite Ha. left. reflexivity.
Qed.
