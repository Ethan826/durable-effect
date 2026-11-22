(** * Further witnesses, added after the independent review of step 2 (its finding F8).

    Each is closed by evaluation in the kernel ([vm_compute]); none adds an axiom. *)

From Coq Require Import List ZArith Bool Arith.
From Durable Require Import Runtime Exec Concrete Rev3 Witnesses.
Import ListNotations.
Open Scope nat_scope.

Definition yields (n : nat) (k : Code) : Code := Nat.iter n (fun c => CYield 0 c) k.

(** The root awaits a sleep; its finalizer yields five times and then reads the clock. *)
Definition slow_finalizer : CProg :=
  {| bodies := fun _ => {| main := CStart (OSleep (Millis 50)) (fun _ => CEnd 0);
                           fin := yields 5 (CClock (fun _ => CEnd 0)) |};
     root_body := 0 |}.

Definition cut_at_two (k : Cut) (stop : option nat) : Schedule :=
  {| arrived := fun _ => 1; cut_at := Some (2, k); stop_at := stop |}.

(** The next attempt starting in the same process stops the closing after a suspension,
    here before the finalizer reads the clock (X6, the owner's decision on #37). *)
Theorem next_attempt_stops_closing :
  run concrete slow_finalizer (inputs first_sample) (cut_at_two Suspended (Some 4)) 60 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; AStart 0 0 (OSleep (Millis 50));
   ACommand 1 (KOp (OSleep (Millis 50))) (Some (0, 0)); ACut Suspended].
Proof. vm_compute. reflexivity. Qed.

(** An [Ended] cut, such as Restate's abort timeout, closes the attempt too (X3, X6). *)
Theorem ended_cut_closes :
  run concrete slow_finalizer (inputs first_sample) (cut_at_two Ended None) 60 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; AStart 0 0 (OSleep (Millis 50));
   ACommand 1 (KOp (OSleep (Millis 50))) (Some (0, 0)); ACut Ended; AClock 0 100;
   AExit (VRoot ExitInterrupted)].
Proof. vm_compute. reflexivity. Qed.

(** The root exits while a forked fiber, whose finalizer yields four times, is still
    queued. *)
Definition closing_with_work : CProg :=
  {| bodies := fun i => match i with
       | O => plain (CFork false 1 (fun _ => CYield 0 (CEnd 0)))
       | _ => {| main := CAwaitCell 9 (fun _ => CEnd 0); fin := yields 4 (CEnd 0) |}
       end;
     root_body := 0 |}.

(** A suspension during closing after the root's exit: closing continues, and its exit is
    recorded after the cut (X3, X6). *)
Theorem cut_during_closing_continues :
  run concrete closing_with_work (inputs first_sample)
    {| arrived := fun _ => 1; cut_at := Some (6, Suspended); stop_at := None |} 60 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ACut Suspended;
   AExit (VRoot (ExitSuccess 0))].
Proof. vm_compute. reflexivity. Qed.

(** A foreign resume during closing after the root's exit is the first violation, and the
    verdict is a defect (definitional choice 13). *)
Theorem foreign_during_closing_is_defect :
  let I := with_foreign first_sample (fun k => if Nat.eqb k 6 then Some (FResume 1) else None) in
  run concrete closing_with_work I (replay I) 60 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; AViolation ForeignResume;
   AExit VDefect].
Proof. vm_compute. reflexivity. Qed.

(** A fiber waiting for the slot that unwinds has its request removed, so its command is
    never issued (X5). *)
Theorem unwound_waiter_is_removed :
  let e := [InNotify 0 (RSample 100); InNotify 1 (ROutcome (Value 0))] in
  let p := {| bodies := fun i => match i with
                | O => plain (CFork false 1 (fun a => CYield 0 (CInterrupt a
                         (CFork false 2 (fun b => CYield 0 (CYield 0 (CInterrupt b (CEnd 0))))))))
                | 1 => plain (CStart (OSleep (Millis 15000)) (fun _ => CEnd 1))
                | _ => plain (CStart (ORun 7 0) (fun _ => CEnd 2))
                end;
              root_body := 0 |} in
  run concrete p (inputs e) (replay (inputs e)) 80 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; AStart 1 0 (OSleep (Millis 15000));
   ACommand 1 (KOp (OSleep (Millis 15000))) (Some (1, 0)); AStart 2 1 (ORun 7 0);
   AExit (VRoot (ExitSuccess 0))].
Proof. vm_compute. reflexivity. Qed.

(** An infinite sleep is an endless chain of 2^31 - 1 ms links, never delivered (P9). *)
Theorem infinite_sleep_is_endless_chain :
  let e := [InNotify 0 (RSample 0); InNotify 1 (ROutcome (Value 0)); InNotify 2 (RSample 1);
            InNotify 3 (ROutcome (Value 0)); InNotify 4 (RSample 2)] in
  let p := {| bodies := fun _ => plain (CStart (OSleep Forever) (fun _ => CEnd 0));
              root_body := 0 |} in
  run concrete p (inputs e) (replay (inputs e)) 60 =
  [ACommand 0 KSample None; ASampled 0 0 0 None; AStart 0 0 (OSleep Forever);
   ACommand 1 (KOp (OSleep (Millis 2147483647))) (Some (0, 0)); ACommand 2 KSample None;
   ASampled 2 1 2147483647 (Some (0, 0, 2147483647%Z));
   ACommand 3 (KOp (OSleep (Millis 2147483647))) (Some (0, 0)); ACommand 4 KSample None;
   ASampled 4 2 4294967294 (Some (0, 0, 2147483647%Z));
   ACommand 5 (KOp (OSleep (Millis 2147483647))) (Some (0, 0))].
Proof. vm_compute. reflexivity. Qed.

(** A chain cancelled during its second link credits only the first (P3, P8). *)
Theorem chain_cancelled_midway :
  let e := [InNotify 0 (RSample 0); InNotify 1 (ROutcome (Value 0)); InNotify 2 (RSample 10);
            InCancel; InNotify 4 (RSample 20)] in
  let p := {| bodies := fun _ => plain (CStart (OSleep (Millis 2147483652)) (fun _ => CEnd 0));
              root_body := 0 |} in
  run concrete p (inputs e) (replay (inputs e)) 60 =
  [ACommand 0 KSample None; ASampled 0 0 0 None; AStart 0 0 (OSleep (Millis 2147483652));
   ACommand 1 (KOp (OSleep (Millis 2147483647))) (Some (0, 0)); ACommand 2 KSample None;
   ASampled 2 10 2147483647 (Some (0, 0, 2147483647%Z));
   ACommand 3 (KOp (OSleep (Millis 5))) (Some (0, 0)); ACommand 4 KSample None;
   ASampled 4 20 2147483647 None; ACancelled 0 0; AExit (VRoot ExitInterrupted)].
Proof. vm_compute. reflexivity. Qed.

Definition zero_sleep_program : CProg :=
  {| bodies := fun _ => plain (CStart (OSleep (Millis 0)) (fun _ => CEnd 0)); root_body := 0 |}.

(** A sleep of 0 ms issues nothing and is delivered at once (definitional choice 11). *)
Theorem zero_sleep_issues_nothing :
  run concrete zero_sleep_program (inputs first_sample) (replay (inputs first_sample)) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; AStart 0 0 (OSleep (Millis 0));
   ADelivered 0 0 (Value 0); AExit (VRoot (ExitSuccess 0))].
Proof. vm_compute. reflexivity. Qed.

(** Where S9's two executors differ besides a cancelled sample: an [L] above 2^53 - 1 is a
    violation here and not under revision 3, which is why S9 needs that condition. *)
Theorem overflow_separates_rev3 :
  let e := [InNotify 0 (RSample 9007199254740995)] in
  run concrete zero_sleep_program (inputs e) (replay (inputs e)) 40 =
  [ACommand 0 KSample None; AViolation Overflow; AExit VDefect] /\
  run3 concrete zero_sleep_program (inputs e) (replay (inputs e)) 40 =
  [ACommand 0 KSample None; ASampled 0 9007199254740995 9007199254740995 None;
   AStart 0 0 (OSleep (Millis 0)); ADelivered 0 0 (Value 0); AExit (VRoot (ExitSuccess 0))].
Proof. vm_compute. split; reflexivity. Qed.

(** A 0 ms sleep's delivery is dropped when its fiber unwinds before the delivery runs (the
    review's finding F6): fiber 1 is never handed a result. *)
Theorem zero_sleep_release_drops_delivery :
  let e := [InNotify 0 (RSample 100); InNotify 1 (ROutcome (Value 3)); InNotify 2 (RSample 101)] in
  let p := {| bodies := fun i => match i with
                | O => plain (CFork false 1 (fun _ => CFork false 2 (fun _ =>
                         CStart (ORun 1 1) (fun _ => CEnd 0))))
                | 1 => plain (CStart (OSleep (Millis 0)) (fun _ => CEnd 5))
                | _ => plain (CInterrupt 1 (CEnd 0))
                end;
              root_body := 0 |} in
  run concrete p (inputs e) (replay (inputs e)) 60 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; AStart 0 0 (ORun 1 1);
   ACommand 1 (KOp (ORun 1 1)) (Some (0, 0)); AStart 1 1 (OSleep (Millis 0));
   ACommand 2 KSample None; ASampled 2 101 101 None; ADelivered 0 0 (Value 3);
   AExit (VRoot (ExitSuccess 0))].
Proof. vm_compute. reflexivity. Qed.
