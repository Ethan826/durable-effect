(** * The scheduling model: definitions D1 to D9 of verification/dossier/scheduling-dossier.md.

    This file and Executor.v are the owner's interface for the proofs: an executable model of
    the deterministic-scheduling executor. The statements are in Statements.v. Agents proving
    statements do not edit these files (proof-dossier, section 7). *)

From Coq Require Import List ZArith Bool Arith.
From ITree Require Import Core.ITreeDefinition.
Import ListNotations.
Open Scope Z_scope.

(** ** D1. Fibers *)

(** A durable operation's kind and arguments, kept abstract. *)
Definition OpKind := nat.
Definition OpArgs := nat.

(** What a durable operation returns to the fiber awaiting it. A cancellation is not an
    outcome: it interrupts the awaiting fiber (design, revision 4). *)
Inductive Outcome := Value (v : nat) | Failure (v : nat).

(** A forked fiber either starts as a queued task or runs nested inside the forking step. *)
Inductive ForkKind := Queued | Immediate.

(** A sleep's requested duration in whole milliseconds, or [Forever]. A fractional duration is
    rounded up before it reaches the model. *)
Inductive Duration := Millis (d : Z) | Forever.

(** The steps of a fiber that the executor sees. A pure step is a [Tau]; finishing is a [Ret].
    [Fork] names the child's body by its index in the program and returns a handle local to
    the attempt, never a process-wide fiber id (restriction R3). [StartAwait] starts a durable
    operation and awaits it; v1 has at most one awaited operation. [ReadRef] and [WriteRef]
    give the program's fibers shared memory, as an Effect [Ref], [Deferred] or [Queue] does:
    review 3's D1 was a root fiber reading a [Ref] that a child fiber writes. *)
Inductive FiberE : Type -> Type :=
| ReadClock : FiberE Z
| Draw : FiberE nat
| Fork : ForkKind -> nat -> FiberE nat
| StartAwait : OpKind -> OpArgs -> FiberE Outcome
| Sleep : Duration -> FiberE unit
| YieldNow : FiberE unit
| Interrupt : nat -> FiberE unit
| WaitOutside : FiberE nat
| ReadRef : nat -> FiberE nat
| WriteRef : nat -> nat -> FiberE unit.

(** A fiber's code: its main body and the finalizer that runs if it is interrupted. *)
Record Body := { main : itree FiberE unit; finalizer : itree FiberE unit }.

(** ** D2. Programs *)

(** A table of bodies and the index of the root's body. Restriction R1 holds by construction:
    fibers reach the outside only through [FiberE]. *)
Record Program := { bodies : nat -> Body; root : nat }.

(** ** D3 and D6. Journal entries and trace actions *)

Inductive Violation := SecondAwait | BlockedWithNothingAwaited | StepOutsideTurn.

Inductive Exit := Succeeded | Defect | Suspended | Crashed.

(** The executor's visible actions, in order. [Command] and [SleepCommand] carry the durable
    operation's index; [Sampled] carries the sample's index; [Delivered] carries the index of
    the operation whose result it hands to fiber [h]; [CancelDelivered] records that operation
    [op] was cancelled, before fiber [h] is interrupted. The journal is the subsequence of
    commands, samples, deliveries and cancellations. *)
Inductive Action :=
| Command (op : nat) (h : nat) (k : OpKind) (a : OpArgs)
| SleepCommand (op : nat) (h : nat) (d : Z)
| SampleCommand (i : nat)
| Sampled (i : nat) (s : Z)
| Delivered (op : nat) (h : nat) (o : option Outcome)
| CancelDelivered (op : nat) (h : nat)
| ClockRead (h : nat) (l : Z)
| Drawn (h : nat) (r : nat)
| Interrupted (h : nat)
| Violated (v : Violation)
| Exited (e : Exit).

(** ** D4. Environments *)

Inductive Ending := EndSuspend | EndCrash.

(** A clock sample: the true time and the error of the host that took it. *)
Record Sample := { true_time : Z; host_error : Z }.
Definition sample_value (s : Sample) : Z := true_time s + host_error s.

(** The choices that are the same in a live attempt and its replay: the outcome of the [n]th
    durable operation, the [n]th clock sample, whether the [n]th operation is cancelled, the
    seeded random stream (seeded with the invocation id), and the point at which the attempt
    ends, counted in progress steps: steps that run a task or deliver a result, not steps that
    wait for an arrival. *)
Record Env := {
  outcome_of : nat -> Outcome;
  sample_of : nat -> Sample;
  cancelled_at : nat -> bool;
  random_of : nat -> nat;
  ends_at : option (nat * Ending)
}.

(** ** D7. Arrival schedules *)

(** [A n i] says whether, at micro-step [i], the result of operation [n] (its completion or its
    cancellation) has arrived. A replay is the schedule in which a journaled result has arrived
    from the start. *)
Definition Arrival := nat -> nat -> bool.
Definition monotone (A : Arrival) : Prop :=
  forall n i j, (i <= j)%nat -> A n i = true -> A n j = true.

(** For S5 only: at micro-step [i], a source outside Restate resumes the fiber with handle [h],
    delivering value [v]. D4's environment has no such resumes. *)
Definition OutsideResumes := nat -> option (nat * nat).
Definition no_outside_resumes : OutsideResumes := fun _ => None.

(** ** D5. Executor state *)

(** The largest single durable sleep; a longer sleep is a chain of these. *)
Definition max_chunk : Z := 2147483647.

(** Operations a fiber takes before the scheduler makes it yield, as in Effect's count. *)
Definition max_ops : nat := 2048.

(** A suspended fiber's continuation, by the type of value that resumes it. *)
Inductive Pending :=
| NoPending
| ResumeOutcome (k : Outcome -> itree FiberE unit)
| ResumeUnit (k : unit -> itree FiberE unit)
| ResumeNat (k : nat -> itree FiberE unit).

(** [Hung] is a fiber that will never resume: revision 3's executor for a sleep it never sends
    to Restate. *)
Inductive Status := Ready | AwaitingDurable | WaitingOutside | Hung | Done.

Record Fiber := {
  handle : nat;
  code : itree FiberE unit;
  fin : itree FiberE unit;
  pending : Pending;
  status : Status;
  interrupted : bool
}.

(** What is left of a sleep after its current chunk: nothing, more milliseconds, or forever. *)
Inductive Chain := NoChain | Remaining (d : Z) | Endless.

(** The awaited operation: the fiber's handle, the operation's index, and for a sleep the
    current chunk and what remains. *)
Inductive Awaited :=
| AwaitOp (h : nat) (op : nat)
| AwaitSleep (h : nat) (op : nat) (chunk : Z) (rest : Chain).

Record State := {
  fibers : list Fiber;
  queue : list nat;
  awaited : option Awaited;
  abandoned : list nat;
  next_op : nat;
  next_sample : nat;
  next_handle : nat;
  draws : nat;
  logical : Z;
  memory : nat -> nat;
  trace : list Action;
  micro : nat;
  progress : nat;
  finished : option Exit
}.

(** The two places where revision 3's executor differs from revision 4's for a program with one
    fiber (S9): revision 4 splits a sleep longer than [max_chunk] into a chain and makes a
    handler blocked with nothing awaited a violation; revision 3 sends a sleep of up to
    2^53 - 1 ms whole, never sends a longer one, and hangs when blocked. *)
Record Policy := { chunk_long_sleeps : bool; blocked_is_violation : bool }.
Definition policy_v1 : Policy := {| chunk_long_sleeps := true; blocked_is_violation := true |}.
Definition policy_rev3 : Policy :=
  {| chunk_long_sleeps := false; blocked_is_violation := false |}.

(** The largest integer JavaScript represents exactly, revision 3's bound on a sleep. *)
Definition max_safe : Z := 9007199254740991.

(** The time rule (#5, design revision 4). [floor] is the slept chunk after a completed sleep,
    and 0 after anything else, including a cancelled sleep. *)
Definition next_logical (l floor s : Z) : Z := Z.max (l + floor) s.

(** ** D8 and D9 are defined in Executor.v, with the executor's step function. *)
