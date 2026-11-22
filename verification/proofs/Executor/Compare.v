(** * The earlier findings on the old model and on the new one (#37, Evidence).

    Each pair runs the same program on the model that #37 replaces (Scheduling) and on the
    executor model of revision 9 with the concrete runtime. The old run shows the finding; the
    new run shows what the design now requires. Findings the old model cannot express, such
    as a cancellation during a sample (#32), appear in Witnesses.v only. *)

From Coq Require Import List ZArith Bool Arith.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Model Executor.
From Durable Require Import Runtime Exec Concrete Witnesses.
Import ListNotations.
Open Scope nat_scope.

Module O := Scheduling.Model.
Module OE := Scheduling.Executor.

Definition old_env (cancelled : nat -> bool) : O.Env :=
  {| O.outcome_of := fun _ => O.Value 7;
     O.sample_of := fun n => {| O.true_time := (100 + Z.of_nat n)%Z; O.host_error := 0%Z |};
     O.cancelled_at := cancelled; O.random_of := fun n => n; O.ends_at := None |}.

Definition never_arrives : O.Arrival := fun _ _ => false.
Definition arrived_already : O.Arrival := fun _ _ => true.

(** ** #31: an interrupted fiber's operation *)

(** Old: the child's operation is abandoned, and the root's command is issued while it is
    still pending, which SDK 1.18.4 rejects with [awaitNext already pending]. *)
Definition old_slot : O.Program :=
  {| O.bodies := fun i => match i with
       | O => {| O.main := Vis (O.Fork O.Queued 1) (fun h => Vis O.YieldNow (fun _ =>
                  Vis (O.Interrupt h) (fun _ => Vis (O.StartAwait 2 0) (fun _ => Ret tt))));
                 O.finalizer := Ret tt |}
       | _ => {| O.main := Vis (O.StartAwait 1 0) (fun _ => Ret tt); O.finalizer := Ret tt |}
       end;
     O.root := 0 |}.

Theorem old_issues_second_while_first_pending :
  OE.run old_slot (old_env (fun _ => false)) never_arrives 60 =
  [O.SampleCommand 0; O.Sampled 0 100; O.Command 0 1 1 0; O.Interrupted 1;
   O.Command 1 0 2 0].
Proof. vm_compute. reflexivity. Qed.

(** New: while the released operation has not settled, the root waits for the slot, and its
    command is not issued. *)
Theorem new_waits_for_released_operation :
  let e := [InNotify 0 (RSample 100)] in
  run concrete slot_program (inputs e) (replay (inputs e)) 60 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0; ARegister 1; AStart 1 0 (OSleep (Millis 15000)); ACommand 1 (KOp (OSleep (Millis 15000))) (Some (1, 0)); AStart 0 1 (OSleep (Millis 3000))].
Proof. vm_compute. reflexivity. Qed.

(** ** #34.1: interrupting a fiber waits for its finalizer *)

(** Old: the parent reads the cell before the child's finalizer writes it, and issues an
    operation of kind 0. *)
Definition old_interrupt : O.Program :=
  {| O.bodies := fun i => match i with
       | O => {| O.main := Vis (O.Fork O.Queued 1) (fun h => Vis O.YieldNow (fun _ =>
                  Vis (O.Interrupt h) (fun _ => Vis (O.ReadRef 0) (fun v =>
                  Vis (O.StartAwait v 0) (fun _ => Ret tt)))));
                 O.finalizer := Ret tt |}
       | _ => {| O.main := Vis O.WaitOutside (fun _ => Ret tt);
                 O.finalizer := Vis O.YieldNow (fun _ => Vis (O.WriteRef 0 1) (fun _ => Ret tt)) |}
       end;
     O.root := 0 |}.

Theorem old_parent_reads_before_finalizer :
  In (O.Command 0 0 0 0) (OE.run old_interrupt (old_env (fun _ => false)) arrived_already 60).
Proof. vm_compute. auto 20. Qed.

(** New: the parent reads 1 ([interrupt_waits_for_finalizer] in Witnesses.v). *)
Theorem new_parent_reads_after_finalizer :
  In (ACommand 1 (KOp (ORun 1 0)) (Some (0, 0)))
     (run concrete interrupt_waits (inputs first_sample) (replay (inputs first_sample)) 60).
Proof. vm_compute. auto 20. Qed.

(** ** #34.2: a cancelled root *)

Definition old_cancelled : O.Program :=
  {| O.bodies := fun _ => {| O.main := Vis (O.StartAwait 1 0) (fun _ => Ret tt);
                             O.finalizer := Ret tt |};
     O.root := 0 |}.

Theorem old_cancelled_root_succeeds :
  In (O.Exited O.Succeeded)
     (OE.run old_cancelled (old_env (fun n => Nat.eqb n 0)) arrived_already 60).
Proof. vm_compute. auto 20. Qed.

Theorem new_cancelled_root_is_interrupted :
  let e := [InNotify 0 (RSample 100); InCancel; InNotify 2 (RSample 101)] in
  let p := {| bodies := fun _ => plain (CStart (ORun 1 0) (fun _ => CEnd 0));
              root_body := 0 |} in
  In (AExit (VRoot ExitInterrupted)) (run concrete p (inputs e) (replay (inputs e)) 40)
  /\ ~ In (AExit (VRoot (ExitSuccess 0))) (run concrete p (inputs e) (replay (inputs e)) 40).
Proof. vm_compute. split; [auto 20 | intuition discriminate]. Qed.

(** ** Review 3's D1 on the new model *)

(** The old model's run is [d1_same_trace] in Scheduling/Witnesses.v. A child writes a cell
    3000 times, which forces a yield at [max_ops]; the root awaits an operation, reads the
    cell, and branches on it. Live and replay agree, and the root saw 3000. *)
Fixpoint writes (n : nat) (k : Code) : Code :=
  match n with O => k | S m => CWrite 0 (3000 - m) (writes m k) end.

Definition d1 : CProg :=
  {| bodies := fun i => match i with
       | O => plain (CFork false 1 (fun _ => CStart (ORun 1 0) (fun _ =>
                CRead 0 (fun seen => if Nat.eqb seen 3000
                                     then CStart (ORun 2 0) (fun _ => CEnd 0)
                                     else CStart (ORun 3 0) (fun _ => CEnd 0)))))
       | _ => plain (writes 3000 (CEnd 0))
       end;
     root_body := 0 |}.

Definition d1_entries : list JIn :=
  [InNotify 0 (RSample 100); InNotify 1 (ROutcome (Value 7)); InNotify 2 (RSample 101)].

Theorem new_d1_live_equals_replay :
  run concrete d1 (inputs d1_entries) (live (inputs d1_entries)) 300 =
  run concrete d1 (inputs d1_entries) (replay (inputs d1_entries)) 300.
Proof. vm_compute. reflexivity. Qed.

Theorem new_d1_reads_final_value :
  In (ACommand 3 (KOp (ORun 2 0)) (Some (0, 1)))
     (run concrete d1 (inputs d1_entries) (replay (inputs d1_entries)) 300).
Proof. vm_compute. auto 30. Qed.
