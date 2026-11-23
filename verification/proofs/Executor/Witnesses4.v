(** * Differences from revision 3's executor, shown in the build.

    The record of S9 lists these; the second independent review found four of them shown
    only by evaluations outside the build (its finding 3). Each theorem states both
    executors' traces for one program, closed by evaluation in the kernel. *)

From Coq Require Import List ZArith Bool Arith.
From Durable Require Import Runtime Exec Concrete Rev3 Witnesses.
Import ListNotations.
Open Scope nat_scope.

(** A sleep longer than 2^31 - 1 ms is a chain of two links here; revision 3 sends it as one
    command. *)
Theorem rev3_differs_on_long_sleep :
  let e := [InNotify 0 (RSample 0); InNotify 1 (ROutcome (Value 0)); InNotify 2 (RSample 10);
            InNotify 3 (ROutcome (Value 0)); InNotify 4 (RSample 20)] in
  let p := {| bodies := fun _ => plain (CStart (OSleep (Millis 2147483652))
                                          (fun _ => CClock (fun _ => CEnd 0)));
              root_body := 0 |} in
  run concrete p (inputs e) (replay (inputs e)) 60 =
  [ACommand 0 KSample None; ASampled 0 0 0 None; ARegister 0;
   AStart 0 0 (OSleep (Millis 2147483652));
   ACommand 1 (KOp (OSleep (Millis 2147483647))) (Some (0, 0)); ACommand 2 KSample None;
   ASampled 2 10 2147483647 (Some (0, 0, 2147483647%Z));
   ACommand 3 (KOp (OSleep (Millis 5))) (Some (0, 0)); ACommand 4 KSample None;
   ASampled 4 20 2147483652 (Some (0, 0, 5%Z)); ADelivered 0 0 (Value 0);
   AClock 0 2147483652; AExit (VRoot (ExitSuccess 0))] /\
  run3 concrete p (inputs e) (replay (inputs e)) 60 =
  [ACommand 0 KSample None; ASampled 0 0 0 None; ARegister 0;
   AStart 0 0 (OSleep (Millis 2147483652));
   ACommand 1 (KOp (OSleep (Millis 2147483652))) (Some (0, 0)); ACommand 2 KSample None;
   ASampled 2 10 2147483652 (Some (0, 0, 2147483652%Z)); ADelivered 0 0 (Value 0);
   AClock 0 2147483652; AExit (VRoot (ExitSuccess 0))].
Proof. vm_compute. split; reflexivity. Qed.

(** A task priority other than 0 is a violation here; revision 3 runs it. *)
Theorem rev3_differs_on_priority :
  let p := {| bodies := fun _ => plain (CYield 1 (CEnd 0)); root_body := 0 |} in
  run concrete p (inputs first_sample) (replay (inputs first_sample)) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0; AViolation Priority;
   AExit VDefect] /\
  run3 concrete p (inputs first_sample) (replay (inputs first_sample)) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0;
   AExit (VRoot (ExitSuccess 0))].
Proof. vm_compute. split; reflexivity. Qed.

(** A root blocked with nothing subscribed is a violation here; revision 3 hangs, so its
    trace stops short of this one. *)
Theorem rev3_differs_on_blocked_root :
  let p := {| bodies := fun _ => plain (CAwaitCell 3 (fun _ => CEnd 0)); root_body := 0 |} in
  run concrete p (inputs first_sample) (replay (inputs first_sample)) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0; AViolation Blocked;
   AExit VDefect] /\
  run3 concrete p (inputs first_sample) (replay (inputs first_sample)) 40 =
  [ACommand 0 KSample None; ASampled 0 100 100 None; ARegister 0].
Proof. vm_compute. split; reflexivity. Qed.

(** An infinite sleep is an endless chain here; revision 3 sends nothing, so its trace stops
    at the start. *)
Theorem rev3_differs_on_infinite_sleep :
  let e := [InNotify 0 (RSample 0); InNotify 1 (ROutcome (Value 0)); InNotify 2 (RSample 1);
            InNotify 3 (ROutcome (Value 0)); InNotify 4 (RSample 2)] in
  let p := {| bodies := fun _ => plain (CStart (OSleep Forever) (fun _ => CEnd 0));
              root_body := 0 |} in
  run concrete p (inputs e) (replay (inputs e)) 60 =
  [ACommand 0 KSample None; ASampled 0 0 0 None; ARegister 0; AStart 0 0 (OSleep Forever);
   ACommand 1 (KOp (OSleep (Millis 2147483647))) (Some (0, 0)); ACommand 2 KSample None;
   ASampled 2 1 2147483647 (Some (0, 0, 2147483647%Z));
   ACommand 3 (KOp (OSleep (Millis 2147483647))) (Some (0, 0)); ACommand 4 KSample None;
   ASampled 4 2 4294967294 (Some (0, 0, 2147483647%Z));
   ACommand 5 (KOp (OSleep (Millis 2147483647))) (Some (0, 0))] /\
  run3 concrete p (inputs e) (replay (inputs e)) 60 =
  [ACommand 0 KSample None; ASampled 0 0 0 None; ARegister 0; AStart 0 0 (OSleep Forever)].
Proof. vm_compute. split; reflexivity. Qed.

(** ** Cancellations that conform to X5 and X6 while the invocation still succeeds

    The second independent review's finding 8. A cancel signal during the initial sample is
    held; these two programs show where it goes, and that the invocation can then succeed. *)

Definition cancel_first : list JIn :=
  [InCancel; InNotify 1 (RSample 100); InNotify 2 (ROutcome (Value 5));
   InNotify 3 (RSample 101)].

(** A released child's finalizer is the next fiber to start a durable operation, so it
    receives the held cancellation (X5); the root, never cancelled, exits successfully. *)
Theorem finalizer_absorbs_held_cancel :
  let p := {| bodies := fun i => match i with
                | O => plain (CFork false 1 (fun c => CYield 0 (CInterrupt c (CEnd 7))))
                | _ => {| main := CStart (ORun 1 0) (fun _ => CEnd 1);
                          fin := CStart (ORun 4 0) (fun _ => CEnd 0) |}
                end;
              root_body := 0 |} in
  run concrete p (inputs cancel_first) (replay (inputs cancel_first)) 80 =
  [ACommand 0 KSample None; ACommand 1 KSample None; ASampled 1 100 100 None;
   ARegister 0; ARegister 1; AStart 1 0 (ORun 1 0); AStart 1 1 (ORun 4 0);
   ACancelled 1 1; AExit (VRoot (ExitSuccess 7))].
Proof. vm_compute. reflexivity. Qed.

(** The root exits while a cancellation is queued for an immediate child; closing delivers no
    further cancellation (X6.1), and the root's success is the verdict. *)
Theorem closing_drops_queued_cancel :
  let p := {| bodies := fun i => match i with
                | O => plain (CFork true 1 (fun _ => CEnd 3))
                | _ => plain (CStart (ORun 1 0) (fun _ => CEnd 1))
                end;
              root_body := 0 |} in
  run concrete p (inputs cancel_first) (replay (inputs cancel_first)) 80 =
  [ACommand 0 KSample None; ACommand 1 KSample None; ASampled 1 100 100 None;
   ARegister 0; ARegister 1; AStart 1 0 (ORun 1 0); AExit (VRoot (ExitSuccess 3))].
Proof. vm_compute. reflexivity. Qed.
