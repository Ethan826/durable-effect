(** * Step domain: [HeldStartIssuesNothing], and a counterexample to [HeldCancelDelivered].

    [HeldStartIssuesNothing] follows from [on_start] alone.

    [HeldCancelDelivered] fails for a runtime that reuses a token.

    The runtime below starts a 0 ms sleep and then an operation with the same fiber and token
    while a cancellation is held. The executor queues the sleep's delivery and the held
    cancellation for the same await; the delivery clears the awaiter, so a second fiber's
    operation is issued while the cancellation is still queued. The runtime breaks I4 (the
    token is started twice), and [HeldCancelDelivered] does not assume [Meets]. *)

From Coq Require Import List ZArith Bool Arith.
From Durable Require Import Runtime Exec Statements Obligations.
Import ListNotations.
Open Scope Z_scope.

Definition reuse_task (s : nat) (t : Task) : Script nat :=
  match t with
  | StartRoot => Emit (EvStart 0%nat 5%nat (OSleep (Millis 0)))
                   (Emit (EvStart 0%nat 5%nat (ORun 1 1)) (Done 1%nat))
  | Deliver 0%nat 5%nat _ => Emit (EvStart 1%nat 6%nat (ORun 2 2)) (Done 2%nat)
  | _ => Done s
  end.

Definition reuse_runtime : Runtime :=
  {| rstate := nat; prog := unit; requiv := eq; init := fun _ _ => 0%nat;
     run_task := reuse_task |}.

Definition reuse_inputs : Inputs :=
  {| entries := [InCancel; InNotify 1%nat (RSample 100)]; persisted := [];
     foreign := fun _ => None; stream := fun n => n; seed := 0 |}.

Definition reuse_schedule : Schedule :=
  {| arrived := replayed reuse_inputs; cut_at := None; stop_at := None |}.

Theorem step_held_cancel_counterexample :
  let x := xs (iterate reuse_runtime reuse_inputs reuse_schedule 2
                 (initial reuse_runtime tt reuse_inputs)) in
  let y := xs (iterate reuse_runtime reuse_inputs reuse_schedule (2 + 2)
                 (initial reuse_runtime tt reuse_inputs)) in
  phase x = POpen /\ held x = true /\ phase y = POpen /\
  skipn (length (trace x)) (trace y) =
    [AStart 0%nat 5%nat (OSleep (Millis 0)); AStart 0%nat 5%nat (ORun 1 1);
     ADelivered 0%nat 5%nat (Value 0); AStart 1%nat 6%nat (ORun 2 2);
     ACommand 2%nat (KOp (ORun 2 2)) (Some (1%nat, 6%nat))].
Proof. vm_compute. repeat split; reflexivity. Qed.

Theorem step_held_cancel_delivered_refuted : ~ HeldCancelDelivered.
Proof.
  intros H.
  destruct (H reuse_runtime tt reuse_inputs reuse_schedule 2%nat 2%nat) as [[f [tok Hin]] | Hno];
    [vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | |].
  - vm_compute in Hin; repeat (destruct Hin as [Hin | Hin]; [discriminate |]); exact Hin.
  - apply (Hno 2%nat (ORun 2 2) (Some (1%nat, 6%nat))); vm_compute; tauto.
Qed.

Theorem step_held_start_issues_nothing : HeldStartIssuesNothing.
Proof.
  intros I x f tok op P V Ha Hh Z; unfold on_start; rewrite P; cbv zeta; rewrite Z.
  cbn [awaiter held emit mk]; rewrite Ha, Hh; cbn; repeat split; reflexivity.
Qed.
