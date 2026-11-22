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
