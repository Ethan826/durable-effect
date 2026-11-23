(** * Proof obligations beyond the statements (dossier, open items).

    Named propositions, with no proof, written by the interface's owner. *)

From Coq Require Import List ZArith Bool Arith.
From Durable Require Import Runtime Exec Concrete Statements.
Import ListNotations.

(** The concrete runtime meets the interface, so [Meets] is met by a runtime with forks,
    masks, finalizers and interruption, and the statements that assume it are not vacuous. *)
Definition MeetsConcrete : Prop := Meets concrete.

(** A fiber cannot unwind while the sample after its operation is pending, so the executor
    never holds a sample it must retire unapplied (definitional choice 8): no reachable
    state's subscription is a [FReleased] sample. *)
Definition ReleasedSampleUnreachable : Prop :=
  forall R p I Sch s, reachable R p I Sch s ->
    forall c f tok k, sub (xs s) <> Some (SSample c (FReleased f tok k)).

(** X5's held cancellation, first form, refuted and kept on record: without [Meets], a
    runtime that starts one token twice makes the executor issue a command while the
    cancellation waits in the queue ([step_held_cancel_delivered_refuted], StepHeld.v). *)
Definition HeldCancelDeliveredFirstForm : Prop :=
  forall R p I Sch n m,
    let x := xs (iterate R I Sch n (initial R p I)) in
    let y := xs (iterate R I Sch (n + m) (initial R p I)) in
    phase x = POpen -> held x = true -> phase y = POpen ->
    let suffix := skipn (length (trace x)) (trace y) in
    (exists f tok, In (ACancelled f tok) suffix) \/
    (forall c op o, ~ In (ACommand c (KOp op) o) suffix).

(** X5: a held cancellation reaches the next fiber that starts a durable operation. For a
    runtime that meets the interface, from a reachable open state with a cancellation held,
    as long as the attempt stays open, no durable command is issued before a cancellation is
    delivered. The combined review found a model in which it was lost when its fiber unwound
    before receiving it (F1). *)
Definition HeldCancelDelivered : Prop :=
  forall R, Meets R -> forall p I Sch n m,
    let x := xs (iterate R I Sch n (initial R p I)) in
    let y := xs (iterate R I Sch (n + m) (initial R p I)) in
    phase x = POpen -> held x = true -> phase y = POpen ->
    let suffix := skipn (length (trace x)) (trace y) in
    (exists f tok, In (ACancelled f tok) suffix) \/
    (forall c op o, ~ In (ACommand c (KOp op) o) suffix).

(** P8's second half, proved where its Coq form only assumes it (the combined review's F4): a
    fiber that starts a durable operation while a cancellation is held issues no command; it
    is queued a cancellation instead. *)
Definition HeldStartIssuesNothing : Prop :=
  forall I x f tok op,
    phase x = POpen -> violated x = false -> awaiter x = None -> held x = true ->
    zero_sleep op = false ->
    trace (on_start I x f tok op) = trace x ++ [AStart f tok op] /\
    held (on_start I x f tok op) = false /\
    queue (on_start I x f tok op) = queue x ++ [DeliverCancel f tok].

(** A run from any runtime state equivalent to the initial one gives the same trace, so the
    statements stated from the initial state (S4, S8) hold for attempts in any process (the
    combined review's F5). *)
Definition RunFromEquivalent : Prop :=
  forall R, Meets R -> forall p I Sch r n,
    requiv R r (init R p (seed I)) -> run_from R p I Sch r n = run R p I Sch n.
