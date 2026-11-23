(** * Arrival: definitions and tactics shared by the proofs of S1, S2, S3 and S10.

    [arrival_sinf] is the schedule under which every entry has arrived and nothing is cut or
    stopped; the run under it is the one every other schedule follows with waiting steps
    inserted. [arrival_strip] forgets the micro-step counter, and [arrival_srel] relates two
    systems whose executor states agree apart from that counter and whose runtime states are
    equivalent. *)

From Coq Require Import List ZArith Bool Arith.
From Durable Require Import Runtime Exec Statements.
Import ListNotations.
Open Scope Z_scope.

(** Every entry has arrived, and there is no cut or stop. *)
Definition arrival_sinf (I : Inputs) : Schedule :=
  {| arrived := fun _ => length (entries I); cut_at := None; stop_at := None |}.

Definition arrival_strip (x : XState) : XState := set_micro x 0.

Definition arrival_srel (R : Runtime) (s1 s2 : Sys R) : Prop :=
  arrival_strip (xs s1) = arrival_strip (xs s2) /\ requiv R (rs s1) (rs s2).

(** A waiting step: only the counter moves. *)
Definition arrival_bump {R} (s : Sys R) : Sys R :=
  {| xs := set_micro (xs s) (S (micro (xs s))); rs := rs s |}.

(** Unfold every field update and projection, so that each field is read off directly. *)
Ltac arrival_norm :=
  cbv beta iota zeta delta [phase queue sub awaiter waiter held logical next_cmd cursor
    draws live root_exit violated trace progress micro fseen set_phase set_queue set_sub
    set_awaiter set_waiter set_held set_logical set_next_cmd set_cursor set_draws set_live
    set_root_exit set_violated set_progress set_micro set_fseen mk emit enqueue].

(** Split on every match, innermost scrutinee first, normalising after each split. *)
Ltac arrival_split :=
  repeat (try reflexivity;
          match goal with
          | |- context [match ?e with _ => _ end] =>
              lazymatch e with
              | existsb _ _ => let E := fresh "D" in destruct e eqn:E
              | context [match _ with _ => _ end] => fail
              | _ => destruct e
              end
          end; arrival_norm).

Lemma arrival_strip_eta : forall x, set_micro (arrival_strip x) (micro x) = x.
Proof. intros []. reflexivity. Qed.

Lemma arrival_strip_micro : forall x m, arrival_strip (set_micro x m) = arrival_strip x.
Proof. reflexivity. Qed.

Lemma arrival_strip_eq : forall x y,
  arrival_strip x = arrival_strip y -> x = set_micro y (micro x).
Proof.
  intros x y H. transitivity (set_micro (arrival_strip x) (micro x)).
  - symmetry. apply arrival_strip_eta.
  - rewrite H. reflexivity.
Qed.

Lemma arrival_emit_micro : forall x m a, emit (set_micro x m) a = set_micro (emit x a) m.
Proof. reflexivity. Qed.

Lemma arrival_trace_set_micro : forall x m, trace (set_micro x m) = trace x.
Proof. reflexivity. Qed.
Lemma arrival_phase_set_micro : forall x m, phase (set_micro x m) = phase x.
Proof. reflexivity. Qed.
Lemma arrival_cursor_set_micro : forall x m, cursor (set_micro x m) = cursor x.
Proof. reflexivity. Qed.
Lemma arrival_progress_set_micro : forall x m, progress (set_micro x m) = progress x.
Proof. reflexivity. Qed.
Lemma arrival_next_cmd_set_micro : forall x m, next_cmd (set_micro x m) = next_cmd x.
Proof. reflexivity. Qed.
