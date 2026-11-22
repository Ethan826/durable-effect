(** * Non-vacuity witnesses for the executor model of #37, revision 9.

    Each theorem runs a program on the concrete runtime and is closed by evaluation in the
    kernel ([vm_compute]); none adds an axiom. Each names the finding or rule it witnesses.
    The old model's runs of the same findings are in Compare.v. *)

From Coq Require Import List ZArith Bool Arith.
From Durable Require Import Runtime Exec Concrete Rev3 Statements.
Import ListNotations.
Open Scope Z_scope.

(** ** Helpers *)

Definition plain (m : Code) : Body := {| main := m; fin := CEnd 0 |}.

Definition inputs (e : list JIn) : Inputs :=
  {| entries := e; persisted := []; foreign := fun _ => None; stream := fun n => n;
     seed := 0 |}.

Definition with_foreign (e : list JIn) (fi : nat -> option Foreign) : Inputs :=
  {| entries := e; persisted := []; foreign := fi; stream := fun n => n; seed := 0 |}.

(** Every entry arrived from the start, as on replay. *)
Definition replay (I : Inputs) : Schedule :=
  {| arrived := replayed I; cut_at := None; stop_at := None |}.

(** One entry arrives every seven micro-steps, as in a live attempt. *)
Definition live (I : Inputs) : Schedule :=
  {| arrived := fun i => Nat.min (length (entries I)) (Nat.div i 7); cut_at := None;
     stop_at := None |}.

Definition first_sample : list JIn := [InNotify 0%nat (RSample 100)].

(** ** #31: a released operation holds the slot *)

(** The root forks a child that awaits a 15 s sleep, interrupts it, then sleeps 3 s, as
    [Effect.timeout] around pure work does with its timer. The child's sleep is released and
    stays subscribed; the root's command is issued only after it settles. *)
Definition slot_program : CProg :=
  {| bodies := fun i => match i with
       | O => plain (CFork false 1 (fun c => CYield 0 (CInterrupt c
                (CStart (OSleep (Millis 3000)) (fun _ => CEnd 0)))))
       | _ => plain (CStart (OSleep (Millis 15000)) (fun _ => CEnd 1))
       end;
     root_body := 0 |}.

Definition slot_entries : list JIn :=
  [InNotify 0%nat (RSample 100); InNotify 1%nat (ROutcome (Value 0)); InNotify 2%nat (ROutcome (Value 0));
   InNotify 3%nat (RSample 3200)].

Theorem released_operation_holds_slot :
  run concrete slot_program (inputs slot_entries) (replay (inputs slot_entries)) 80 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0%nat; ARegister 1%nat; AStart 1%nat 0%nat (OSleep (Millis 15000)); ACommand 1 (KOp (OSleep (Millis 15000))) (Some (1%nat, 0%nat)); AStart 0%nat 1%nat (OSleep (Millis 3000)); ACommand 2 (KOp (OSleep (Millis 3000))) (Some (0%nat, 1%nat)); ACommand 3 KSample None; ASampled 3 3200 3200 (Some (0%nat, 1%nat, 3000)); ADelivered 0%nat 1%nat (Value 0); AExit (VRoot (ExitSuccess 0))].
Proof. vm_compute. reflexivity. Qed.

(** S1's instance: the live attempt gives the same trace. *)
Theorem released_operation_live_same :
  run concrete slot_program (inputs slot_entries) (live (inputs slot_entries)) 200 =
  run concrete slot_program (inputs slot_entries) (replay (inputs slot_entries)) 80.
Proof. vm_compute. reflexivity. Qed.

(** A cancel signal while the released sleep holds the slot is held, and delivered to the
    root, whose command is never issued (X5). *)
Theorem held_cancellation_reaches_waiter :
  let e := [InNotify 0%nat (RSample 100); InCancel] in
  run concrete slot_program (inputs e) (replay (inputs e)) 80 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0%nat; ARegister 1%nat; AStart 1%nat 0%nat (OSleep (Millis 15000)); ACommand 1 (KOp (OSleep (Millis 15000))) (Some (1%nat, 0%nat)); AStart 0%nat 1%nat (OSleep (Millis 3000)); ACancelled 0%nat 1%nat; AExit (VRoot ExitInterrupted)].
Proof. vm_compute. reflexivity. Qed.

(** ** Cancellations and samples *)

Definition one_run : CProg :=
  {| bodies := fun _ => plain (CYield 0 (CStart (ORun 4%nat 0%nat) (fun _ => CEnd 0)));
     root_body := 0 |}.

(** A cancel signal with nothing subscribed reaches the next command's wait, and the row for
    a cancelled operation and its sample apply (X5, unobserved). *)
Theorem unobserved_cancel_reaches_next_command :
  let e := [InNotify 0%nat (RSample 100); InCancel; InNotify 2%nat (RSample 101)] in
  run concrete one_run (inputs e) (replay (inputs e)) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0%nat; AStart 0%nat 0%nat (ORun 4 0); ACommand 1 (KOp (ORun 4 0)) (Some (0%nat, 0%nat)); ACommand 2 KSample None; ASampled 2 101 101 None; ACancelled 0%nat 0%nat; AExit (VRoot ExitInterrupted)].
Proof. vm_compute. reflexivity. Qed.

(** #32: a cancel signal while a sample is subscribed retires it and issues a replacement;
    the retired sample's late value, 99, changes nothing (X2, S11). *)
Definition sample_cancel_entries : list JIn :=
  [InNotify 0%nat (RSample 100); InNotify 1%nat (ROutcome (Value 9)); InCancel;
   InNotify 2%nat (RSample 99); InNotify 3%nat (RSample 102)].

Theorem cancel_during_sample_replaces_it :
  run concrete one_run (inputs sample_cancel_entries)
    (replay (inputs sample_cancel_entries)) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0%nat; AStart 0%nat 0%nat (ORun 4 0); ACommand 1 (KOp (ORun 4 0)) (Some (0%nat, 0%nat)); ACommand 2 KSample None; ACommand 3 KSample None; ASampled 3 102 102 None; ACancelled 0%nat 0%nat; AExit (VRoot ExitInterrupted)].
Proof. vm_compute. reflexivity. Qed.

(** Revision 3 records a defect at the same point: S9_cancel's second case. *)
Theorem rev3_cancel_during_sample_is_defect :
  run3 concrete one_run (inputs sample_cancel_entries)
    (replay (inputs sample_cancel_entries)) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0%nat; AStart 0%nat 0%nat (ORun 4 0); ACommand 1 (KOp (ORun 4 0)) (Some (0%nat, 0%nat)); ACommand 2 KSample None; AExit VDefect].
Proof. vm_compute. reflexivity. Qed.

(** A cancel signal during the initial sample issues a replacement; the cancellation is held
    and goes to the first fiber that starts a durable operation, with no command (X2, X5). *)
Theorem cancel_during_initial_sample_is_held :
  let e := [InCancel; InNotify 1%nat (RSample 100)] in
  run concrete one_run (inputs e) (replay (inputs e)) 40 =
  [ACommand 0 KSample None; ACommand 1 KSample None; ASampled 1 100 100 None; ARegister 0%nat; AStart 0%nat 0%nat (ORun 4 0); ACancelled 0%nat 0%nat; AExit (VRoot ExitInterrupted)].
Proof. vm_compute. reflexivity. Qed.

(** A terminal failure of a sample ends the attempt with a defect (X2). *)
Theorem terminal_sample_failure_is_defect :
  let e := [InNotify 0%nat (RSample 100); InNotify 1%nat (ROutcome (Value 2));
            InNotify 2%nat RSampleTerminal] in
  run concrete one_run (inputs e) (replay (inputs e)) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0%nat; AStart 0%nat 0%nat (ORun 4 0); ACommand 1 (KOp (ORun 4 0)) (Some (0%nat, 0%nat)); ACommand 2 KSample None; AViolation SampleTerminal; AExit VDefect].
Proof. vm_compute. reflexivity. Qed.

(** ** A crash during a sample, and its replay (S2) *)

Definition crash_entries : list JIn :=
  [InNotify 0%nat (RSample 100); InNotify 1%nat (ROutcome (Value 2)); InNotify 2%nat (RSample 105)].

Definition crash_during_sample : Schedule :=
  {| arrived := fun i => Nat.min 3 i; cut_at := Some (4%nat, Crashed); stop_at := None |}.

Theorem crash_during_sample_cuts :
  run concrete one_run (inputs crash_entries) crash_during_sample 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0%nat; AStart 0%nat 0%nat (ORun 4 0); ACommand 1 (KOp (ORun 4 0)) (Some (0%nat, 0%nat)); ACommand 2 KSample None; ACut Crashed].
Proof. vm_compute. reflexivity. Qed.

Definition replay_inputs (persist : list CmdKind) : Inputs :=
  {| entries := crash_entries; persisted := persist; foreign := fun _ => None;
     stream := fun n => n; seed := 0 |}.

(** The replay reissues the persisted commands and completes. *)
Theorem crash_replay_completes :
  run concrete one_run (replay_inputs [KSample; KOp (ORun 4%nat 0%nat); KSample])
    (replay (inputs crash_entries)) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0%nat; AStart 0%nat 0%nat (ORun 4 0); ACommand 1 (KOp (ORun 4 0)) (Some (0%nat, 0%nat)); ACommand 2 KSample None; ASampled 2 105 105 None; ADelivered 0%nat 0%nat (Value 2); AExit (VRoot (ExitSuccess 0))].
Proof. vm_compute. reflexivity. Qed.

(** Negative control for S2's check: a journal holding a different command fails the replay
    with a mismatch. *)
Theorem different_journal_mismatches :
  run concrete one_run (replay_inputs [KSample; KOp (ORun 5%nat 0%nat)])
    (replay (inputs crash_entries)) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0%nat; AStart 0%nat 0%nat (ORun 4 0); AExit VMismatch].
Proof. vm_compute. reflexivity. Qed.

(** ** Violations *)

(** [Effect.all] of a timeout's timer and another durable operation: two at once (S4). *)
Theorem two_operations_at_once :
  let p := {| bodies := fun i => match i with
                | O => plain (CFork false 1 (fun _ => CStart (ORun 4%nat 0%nat) (fun _ => CEnd 0)))
                | _ => plain (CStart (OSleep (Millis 50)) (fun _ => CEnd 0))
                end;
              root_body := 0 |} in
  run concrete p (inputs first_sample) (replay (inputs first_sample)) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0%nat; AStart 0%nat 0%nat (ORun 4 0); ACommand 1 (KOp (ORun 4 0)) (Some (0%nat, 0%nat)); ARegister 1%nat; AStart 1%nat 1%nat (OSleep (Millis 50)); AViolation SecondOp; AExit VDefect].
Proof. vm_compute. reflexivity. Qed.

(** #33: a task queued with a priority other than 0 is a violation. *)
Theorem nonzero_priority_is_violation :
  let p := {| bodies := fun _ => plain (CYield 1 (CEnd 0)); root_body := 0 |} in
  run concrete p (inputs first_sample) (replay (inputs first_sample)) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0%nat; AViolation Priority; AExit VDefect].
Proof. vm_compute. reflexivity. Qed.

(** A root blocked with nothing subscribed (S6). *)
Theorem blocked_root_is_violation :
  let p := {| bodies := fun _ => plain (CAwaitCell 3 (fun _ => CEnd 0)); root_body := 0 |} in
  run concrete p (inputs first_sample) (replay (inputs first_sample)) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0%nat; AViolation Blocked; AExit VDefect].
Proof. vm_compute. reflexivity. Qed.

Definition drawing : CProg :=
  {| bodies := fun _ => plain (CDraw (fun _ => CYield 0 (CDraw (fun _ => CEnd 0))));
     root_body := 0 |}.

Definition foreign_at_one (fi : Foreign) : nat -> option Foreign :=
  fun k => if Nat.eqb k 1 then Some fi else None.

(** A foreign resume, a foreign interruption and a resume for a token not awaited are each a
    violation, recorded before the root's first step (S5, I3, I4). *)
Theorem foreign_resume_is_violation :
  let I := with_foreign first_sample (foreign_at_one (FResume 0%nat)) in
  run concrete drawing I (replay I) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; AViolation ForeignResume; ARegister 0%nat; AExit VDefect].
Proof. vm_compute. reflexivity. Qed.

Theorem foreign_interrupt_is_violation :
  let I := with_foreign first_sample (foreign_at_one (FInterrupt 0%nat)) in
  run concrete drawing I (replay I) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; AViolation ForeignInterrupt; ARegister 0%nat; AExit VDefect].
Proof. vm_compute. reflexivity. Qed.

Theorem unawaited_resume_is_violation :
  let I := with_foreign first_sample (foreign_at_one (FResumeToken 7%nat)) in
  run concrete drawing I (replay I) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; AViolation ResumeUnawaited; ARegister 0%nat; AExit VDefect].
Proof. vm_compute. reflexivity. Qed.

(** An [L] above 2^53 - 1 is a violation (P6). *)
Theorem overflow_is_violation :
  let e := [InNotify 0%nat (RSample 9007199254740990); InNotify 1%nat (ROutcome (Value 0));
            InNotify 2%nat (RSample 9007199254740995)] in
  let p := {| bodies := fun _ => plain (CStart (OSleep (Millis 10)) (fun _ => CEnd 0));
              root_body := 0 |} in
  run concrete p (inputs e) (replay (inputs e)) 40 =
  [ACommand 0 KSample None; ASampled 0 9007199254740990 9007199254740990 None; ARegister 0%nat; AStart 0%nat 0%nat (OSleep (Millis 10)); ACommand 1 (KOp (OSleep (Millis 10))) (Some (0%nat, 0%nat)); ACommand 2 KSample None; AViolation Overflow; AExit VDefect].
Proof. vm_compute. reflexivity. Qed.

(** ** Fibers: masks, interruption and closing *)

(** A fiber whose await is inside a mask keeps it when interrupted, accepts the delivery,
    and unwinds once the mask ends (I4, fourth review). *)
Theorem masked_await_is_delivered :
  let p := {| bodies := fun i => match i with
                | O => plain (CFork false 1 (fun c => CYield 0 (CInterrupt c (CEnd 0))))
                | _ => {| main := CMaskOn (CStart (ORun 4%nat 0%nat) (fun _ => CMaskOff (CEnd 7)));
                          fin := CEnd 0 |}
                end;
              root_body := 0 |} in
  let e := [InNotify 0%nat (RSample 100); InNotify 1%nat (ROutcome (Value 3));
            InNotify 2%nat (RSample 101)] in
  run concrete p (inputs e) (replay (inputs e)) 60 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0%nat; ARegister 1%nat; AStart 1%nat 0%nat (ORun 4 0); ACommand 1 (KOp (ORun 4 0)) (Some (1%nat, 0%nat)); ACommand 2 KSample None; ASampled 2 101 101 None; ADelivered 1%nat 0%nat (Value 3); AExit (VRoot (ExitSuccess 0))].
Proof. vm_compute. reflexivity. Qed.

(** #34.1: interrupting a fiber waits for its finalizer, so the parent reads the value the
    finalizer wrote, 1, and issues an operation of kind 1. *)
Definition interrupt_waits : CProg :=
  {| bodies := fun i => match i with
       | O => plain (CFork false 1 (fun c => CYield 0 (CInterrupt c
                (CRead 0 (fun v => CStart (ORun v 0%nat) (fun _ => CEnd 0))))))
       | _ => {| main := CAwaitCell 9 (fun _ => CEnd 0);
                 fin := CYield 0 (CWrite 0 1 (CEnd 0)) |}
       end;
     root_body := 0 |}.

Theorem interrupt_waits_for_finalizer :
  In (ACommand 1%nat (KOp (ORun 1%nat 0%nat)) (Some (0%nat, 0%nat)))
     (run concrete interrupt_waits (inputs first_sample) (replay (inputs first_sample)) 60).
Proof. vm_compute. auto 20. Qed.

(** #34.2: a cancelled root exits interrupted, not successfully. *)
Theorem cancelled_root_exits_interrupted :
  let e := [InNotify 0%nat (RSample 100); InCancel; InNotify 2%nat (RSample 101)] in
  let p := {| bodies := fun _ => plain (CStart (ORun 1%nat 0%nat) (fun _ => CEnd 0));
              root_body := 0 |} in
  In (AExit (VRoot ExitInterrupted)) (run concrete p (inputs e) (replay (inputs e)) 40).
Proof. vm_compute. auto 20. Qed.

(** Fifth review: a detached fork still queued when the root exits registers during closing
    and is interrupted before its first step, so its durable start never happens (X6.3). *)
Theorem fork_registering_in_closing_never_steps :
  let p := {| bodies := fun i => match i with
                | O => plain (CFork false 1 (fun _ => CEnd 0))
                | _ => plain (CStart (ORun 4%nat 0%nat) (fun _ => CEnd 0))
                end;
              root_body := 0 |} in
  run concrete p (inputs first_sample) (replay (inputs first_sample)) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0%nat; ARegister 1%nat; AExit (VRoot (ExitSuccess 0))].
Proof. vm_compute. reflexivity. Qed.

(** A durable start in a finalizer during closing is refused with a defect; the finalizer
    ends, and the verdict is the root's exit (X6.3). *)
Theorem start_in_closing_is_refused :
  let p := {| bodies := fun i => match i with
                | O => plain (CFork false 1 (fun _ => CEnd 0))
                | _ => {| main := CEnd 0; fin := CStart (ORun 4%nat 0%nat) (fun _ => CEnd 0) |}
                end;
              root_body := 0 |} in
  run concrete p (inputs first_sample) (replay (inputs first_sample)) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0%nat; ARegister 1%nat; AStart 1%nat 0%nat (ORun 4 0); ARefused 1%nat 0%nat; AExit (VRoot (ExitSuccess 0))].
Proof. vm_compute. reflexivity. Qed.

(** An attempt suspended while the root awaits a sleep closes after the cut: the root's
    finalizer runs (it reads the clock), and the exit is recorded after the cut, where no
    statement compares it (X6). *)
Theorem suspension_runs_finalizers :
  let p := {| bodies := fun _ => {| main := CStart (OSleep (Millis 50)) (fun _ => CEnd 0);
                                    fin := CClock (fun _ => CEnd 0) |};
              root_body := 0 |} in
  let Sch := {| arrived := fun _ => 1%nat; cut_at := Some (2%nat, Suspended);
                stop_at := None |} in
  run concrete p (inputs first_sample) Sch 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0%nat; AStart 0%nat 0%nat (OSleep (Millis 50)); ACommand 1 (KOp (OSleep (Millis 50))) (Some (0%nat, 0%nat)); ACut Suspended; AClock 0%nat 100; AExit (VRoot ExitInterrupted)].
Proof. vm_compute. reflexivity. Qed.

(** ** The time rule *)

(** A sleep of 2^31 + 4 ms is two links, credited 2^31 - 1 and 5 ms (P3, P9). *)
Theorem long_sleep_is_a_chain :
  let e := [InNotify 0%nat (RSample 0); InNotify 1%nat (ROutcome (Value 0)); InNotify 2%nat (RSample 10);
            InNotify 3%nat (ROutcome (Value 0)); InNotify 4%nat (RSample 20)] in
  let p := {| bodies := fun _ => plain (CStart (OSleep (Millis 2147483652))
                                          (fun _ => CClock (fun _ => CEnd 0)));
              root_body := 0 |} in
  run concrete p (inputs e) (replay (inputs e)) 60 =
  [ACommand 0 KSample None; ASampled 0 0 0 None; ARegister 0%nat; AStart 0%nat 0%nat (OSleep (Millis 2147483652)); ACommand 1 (KOp (OSleep (Millis 2147483647))) (Some (0%nat, 0%nat)); ACommand 2 KSample None; ASampled 2 10 2147483647 (Some (0%nat, 0%nat, 2147483647)); ACommand 3 (KOp (OSleep (Millis 5))) (Some (0%nat, 0%nat)); ACommand 4 KSample None; ASampled 4 20 2147483652 (Some (0%nat, 0%nat, 5)); ADelivered 0%nat 0%nat (Value 0); AClock 0%nat 2147483652; AExit (VRoot (ExitSuccess 0))].
Proof. vm_compute. reflexivity. Qed.

(** #35: a sleep cancelled after its timer fired but before its sample was applied credits
    nothing, so P5's early-fire hypothesis has no chunk to apply to. *)
Theorem cancelled_link_credits_nothing :
  let e := [InNotify 0%nat (RSample 100); InNotify 1%nat (ROutcome (Value 0)); InCancel;
            InNotify 3%nat (RSample 100)] in
  let p := {| bodies := fun _ => plain (CStart (OSleep (Millis 10)) (fun _ => CEnd 0));
              root_body := 0 |} in
  run concrete p (inputs e) (replay (inputs e)) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0%nat; AStart 0%nat 0%nat (OSleep (Millis 10)); ACommand 1 (KOp (OSleep (Millis 10))) (Some (0%nat, 0%nat)); ACommand 2 KSample None; ACommand 3 KSample None; ASampled 3 100 100 None; ACancelled 0%nat 0%nat; AExit (VRoot ExitInterrupted)].
Proof. vm_compute. reflexivity. Qed.

(** ** S9: one fiber agrees with revision 3 *)

Theorem single_fiber_agrees_with_rev3 :
  let e := [InNotify 0%nat (RSample 100); InNotify 1%nat (ROutcome (Value 9)); InNotify 2%nat (RSample 101);
            InNotify 3%nat (ROutcome (Value 0)); InNotify 4%nat (RSample 103)] in
  let p := {| bodies := fun _ => plain (CYield 0 (CStart (ORun 4%nat 0%nat) (fun _ => CDraw (fun _ =>
                         CStart (OSleep (Millis 5)) (fun _ => CClock (fun _ => CEnd 0))))));
              root_body := 0 |} in
  run concrete p (inputs e) (replay (inputs e)) 60 = run3 concrete p (inputs e) (replay (inputs e)) 60.
Proof. vm_compute. reflexivity. Qed.

(** ** Negative controls *)

(** Different notification values give different traces, so S1 does not hold for want of
    anything to distinguish. *)
Theorem values_change_traces :
  let e1 := [InNotify 0%nat (RSample 100); InNotify 1%nat (ROutcome (Value 1)); InNotify 2%nat (RSample 101)] in
  let e2 := [InNotify 0%nat (RSample 100); InNotify 1%nat (ROutcome (Value 2)); InNotify 2%nat (RSample 101)] in
  run concrete one_run (inputs e1) (replay (inputs e1)) 40 <>
  run concrete one_run (inputs e2) (replay (inputs e2)) 40.
Proof. vm_compute. discriminate. Qed.

(** Where the foreign input arrives changes the trace, so S3's inputs must include it. *)
Theorem foreign_position_matters :
  let I1 := with_foreign first_sample (foreign_at_one (FResume 0%nat)) in
  let I2 := with_foreign first_sample (fun k => if Nat.eqb k 2 then Some (FResume 0%nat) else None) in
  run concrete drawing I1 (replay I1) 40 <> run concrete drawing I2 (replay I2) 40.
Proof. vm_compute. discriminate. Qed.
