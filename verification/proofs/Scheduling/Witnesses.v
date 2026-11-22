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
