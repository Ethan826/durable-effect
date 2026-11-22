(** * Non-vacuity witnesses and a refutation (proof-dossier, sections 2 and 4).

    Each theorem is closed by evaluation in the kernel ([vm_compute]); none adds an axiom. *)

From Coq Require Import List ZArith Bool Arith.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model Executor Statements.
Import ListNotations.
Open Scope nat_scope.

(** ** Review 3's D1, as an instance of S1 *)

(** A child fiber writes a shared cell 3000 times, which forces an automatic yield at
    [max_ops]. The root forks it, awaits a durable operation, reads the cell, and chooses its
    next operation by the value it reads. Under the previous design the live attempt and the
    replay took different branches. *)
Fixpoint writes (n : nat) : itree FiberE unit :=
  match n with O => Ret tt | S m => Vis (WriteRef 0 (3000 - m)) (fun _ => writes m) end.

Definition d1_root : itree FiberE unit :=
  Vis (Fork Queued 1) (fun _ =>
  Vis (StartAwait 1 0) (fun _ =>
  Vis (ReadRef 0) (fun seen =>
  if Nat.eqb seen 3000 then Vis (StartAwait 2 0) (fun _ => Ret tt)
  else Vis (StartAwait 3 0) (fun _ => Ret tt)))).

Definition d1_program : Program :=
  {| bodies := fun i => match i with
       | 0 => {| main := d1_root; finalizer := Ret tt |}
       | _ => {| main := writes 3000; finalizer := Ret tt |} end;
     root := 0 |}.

Definition d1_env : Env :=
  {| outcome_of := fun _ => Value 7;
     sample_of := fun n => {| true_time := (100 + Z.of_nat n)%Z; host_error := 0%Z |};
     cancelled_at := fun _ => false; random_of := fun n => n; ends_at := None |}.

Definition live_late : Arrival := fun _ i => Nat.leb 50 i.
Definition replayed : Arrival := fun _ _ => true.

(** The live attempt and the replay produce the same trace. *)
Theorem d1_same_trace :
  run d1_program d1_env live_late 200 = run d1_program d1_env replayed 200.
Proof. vm_compute. reflexivity. Qed.

(** And the branch saw the child's final value: the root's second command has kind 2. *)
Theorem d1_reads_final_value :
  In (Command 1 0 2 0) (run d1_program d1_env live_late 200).
Proof. vm_compute. auto 20. Qed.

(** ** Negative control *)

(** S1 is not true for the wrong reason: different values give different traces. *)
Definition d1_env_other : Env :=
  {| outcome_of := fun _ => Value 7;
     sample_of := fun n => {| true_time := (500 + Z.of_nat n)%Z; host_error := 0%Z |};
     cancelled_at := fun _ => false; random_of := fun n => n; ends_at := None |}.

Theorem values_change_traces :
  run d1_program d1_env replayed 200 <> run d1_program d1_env_other replayed 200.
Proof. vm_compute. discriminate. Qed.

(** ** Refutation of P5 as approved *)

(** The approved P5 bounded [L] by true time plus host error plus one server-clock lead. Two
    1 ms sleeps whose timers fire with no true time passing (lead 1 ms) leave [L] at 102 while
    true time is 100 and host error 0: beyond the single-lead bound of 101. The lead adds up
    per sleep, as the corrected S8_upper states. *)
Definition two_sleeps : Program :=
  {| bodies := fun _ => {| main := Vis (Sleep (Millis 1)) (fun _ =>
                                   Vis (Sleep (Millis 1)) (fun _ => Ret tt));
                           finalizer := Ret tt |};
     root := 0 |}.

Definition frozen_time : Env :=
  {| outcome_of := fun _ => Value 0;
     sample_of := fun _ => {| true_time := 100%Z; host_error := 0%Z |};
     cancelled_at := fun _ => false; random_of := fun n => n; ends_at := None |}.

Theorem p5_single_lead_refuted :
  let st := iterate policy_v1 two_sleeps frozen_time replayed no_outside_resumes 20
              (initial two_sleeps frozen_time) in
  logical st = 102%Z /\ (logical st > 100 + 0 + 1)%Z.
Proof. vm_compute. split; reflexivity. Qed.

(** ** Regression: a fiber is queued at most once *)

(** The root forks a child and interrupts it while the child is still queued. The child's
    finalizer awaits the program's only durable operation. Before the fix the child was queued
    twice, and its second task re-ran the await and recorded [SecondAwait]. *)
Definition queued_twice : Program :=
  {| bodies := fun i => match i with
       | 0 => {| main := Vis (Fork Queued 1) (fun c => Vis (Interrupt c) (fun _ => Ret tt));
                 finalizer := Ret tt |}
       | _ => {| main := Ret tt; finalizer := Vis (StartAwait 9 0) (fun _ => Ret tt) |} end;
     root := 0 |}.

Definition queued_twice_env : Env :=
  {| outcome_of := fun n => Value n;
     sample_of := fun _ => {| true_time := 100%Z; host_error := 0%Z |};
     cancelled_at := fun _ => false; random_of := fun n => n; ends_at := None |}.

(** The command is issued, and no [SecondAwait] is recorded. *)
Theorem queued_twice_no_second_await :
  In (Command 0 1 9 0) (run queued_twice queued_twice_env replayed 30) /\
  ~ In (Violated SecondAwait) (run queued_twice queued_twice_env replayed 30).
Proof. vm_compute. split; [auto 10 | intuition discriminate]. Qed.

(** ** Regression: a delivered cancellation is not an abandonment *)

(** The root awaits one durable operation, which is cancelled. Before the fix, [deliver]
    interrupted the root while the operation was still awaited, and the interruption recorded
    it as abandoned. *)
Definition one_await : Program :=
  {| bodies := fun _ => {| main := Vis (StartAwait 5 0) (fun _ => Ret tt);
                           finalizer := Ret tt |};
     root := 0 |}.

Definition cancels_first : Env :=
  {| outcome_of := fun _ => Value 7;
     sample_of := fun n => {| true_time := (100 + Z.of_nat n)%Z; host_error := 0%Z |};
     cancelled_at := fun n => Nat.eqb n 0; random_of := fun n => n; ends_at := None |}.

Theorem cancelled_not_abandoned :
  In (CancelDelivered 0 0) (run one_await cancels_first replayed 2) /\
  abandoned (iterate policy_v1 one_await cancels_first replayed no_outside_resumes 2
               (initial one_await cancels_first)) = [].
Proof. vm_compute. split; [auto 10 | reflexivity]. Qed.

(** ** An instance of S11 *)

(** The root forks a child that awaits operation 0, yields so that the child runs, interrupts
    it, and awaits operation 1. Operation 0 is abandoned. One environment cancels it and gives
    it outcome 1, the other completes it with outcome 2; the traces are the same. *)
Definition abandons : Program :=
  {| bodies := fun i => match i with
       | 0 => {| main := Vis (Fork Queued 1) (fun c => Vis YieldNow (fun _ =>
                         Vis (Interrupt c) (fun _ => Vis (StartAwait 2 0) (fun _ => Ret tt))));
                 finalizer := Ret tt |}
       | _ => {| main := Vis (StartAwait 1 0) (fun _ => Ret tt); finalizer := Ret tt |} end;
     root := 0 |}.

Definition abandoned_env (cancel0 : bool) (v : nat) : Env :=
  {| outcome_of := fun n => if Nat.eqb n 0 then Value v else Value 9;
     sample_of := fun n => {| true_time := (100 + Z.of_nat n)%Z; host_error := 0%Z |};
     cancelled_at := fun n => andb cancel0 (Nat.eqb n 0); random_of := fun n => n;
     ends_at := None |}.

Theorem abandonment_is_silent :
  In 0 (abandoned (iterate policy_v1 abandons (abandoned_env true 1) replayed
          no_outside_resumes 3 (initial abandons (abandoned_env true 1)))) /\
  In (Delivered 1 0 (Some (Value 9))) (run abandons (abandoned_env true 1) replayed 30) /\
  run abandons (abandoned_env true 1) replayed 30
    = run abandons (abandoned_env false 2) replayed 30.
Proof. vm_compute. split; [auto | split; [auto 10 | reflexivity]]. Qed.

(** ** Why S9's condition changed *)

(** A single fiber that sleeps forever. Revision 3 hangs and issues no sleep command, so the
    condition approved in #28 (every sleep command revision 3 issues is at most [max_chunk])
    holds; revision 4 starts a chain, and the traces differ. *)
Definition sleeps_forever : Program :=
  {| bodies := fun _ => {| main := Vis (Sleep Forever) (fun _ => Ret tt); finalizer := Ret tt |};
     root := 0 |}.

Theorem s9_old_condition_too_weak :
  (forall a, In a (run_rev3 sleeps_forever frozen_time replayed 6) ->
     match a with SleepCommand _ _ _ => False | _ => True end) /\
  run sleeps_forever frozen_time replayed 6 <> run_rev3 sleeps_forever frozen_time replayed 6.
Proof.
  vm_compute. split; [intros a [<-|[<-|[]]]; exact I | discriminate].
Qed.
