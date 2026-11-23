(** * Witnesses added after the combined review of the step 3 proofs.

    Each is closed by evaluation in the kernel ([vm_compute]); none adds an axiom. *)

From Coq Require Import List ZArith Bool Arith.
From Durable Require Import Runtime Exec Concrete Witnesses.
Import ListNotations.
Open Scope nat_scope.

(** The combined review's F1. A cancellation held from the initial sample is queued for the
    child's start; the root interrupts the child before the child receives it, as
    [Effect.race] does when the other side wins. The cancellation is held again, and the
    root's next start receives it with no command issued (X5). Before the fix the root's
    operation was issued and the cancelled invocation succeeded. *)
Theorem held_cancel_survives_release :
  let e := [InCancel; InNotify 1 (RSample 100); InNotify 2 (ROutcome (Value 5));
            InNotify 3 (RSample 101)] in
  let p := {| bodies := fun i => match i with
                | O => plain (CFork false 1 (fun c => CYield 0 (CInterrupt c
                         (CStart (ORun 2 0) (fun _ => CEnd 7)))))
                | _ => plain (CStart (ORun 1 0) (fun _ => CEnd 1))
                end;
              root_body := 0 |} in
  run concrete p (inputs e) (replay (inputs e)) 60 =
  [ACommand 0 KSample None; ACommand 1 KSample None; ASampled 1 100 100 None;
   ARegister 0; ARegister 1; AStart 1 0 (ORun 1 0); AStart 0 1 (ORun 2 0);
   ACancelled 0 1; AExit (VRoot ExitInterrupted)].
Proof. vm_compute. reflexivity. Qed.
