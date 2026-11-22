(** * Statements S1 to S11 of verification/dossier/scheduling-dossier.md, revision 2.

    The owner approved these statements on 2026-11-21 (#28). Each is a named proposition with
    no proof. A statement that changes needs approving again (proof-dossier, section 3). Proofs
    take the form [Theorem s1 : S1.] in separate files. *)

From Coq Require Import List ZArith Bool Arith.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model Executor.
Import ListNotations.
Open Scope Z_scope.

(** ** Helpers *)

(** [l1] is a prefix of [l2]. *)
Definition prefix {X} (l1 l2 : list X) : Prop := exists rest, l2 = l1 ++ rest.

(** Two finite traces of the same attempt: one extends the other. Statements about a whole
    attempt are about every finite prefix of it (dossier, definitional choices). *)
Definition compatible {X} (l1 l2 : list X) : Prop := prefix l1 l2 \/ prefix l2 l1.

(** The environments agree on everything except the arrival schedule, which is not in [Env],
    and the point at which the attempt ends. *)
Definition same_values (E1 E2 : Env) : Prop :=
  (forall n, outcome_of E1 n = outcome_of E2 n) /\
  (forall n, sample_of E1 n = sample_of E2 n) /\
  (forall n, cancelled_at E1 n = cancelled_at E2 n) /\
  (forall n, random_of E1 n = random_of E2 n).

(** The environments agree on the first [ops] operation results and the first [samples]
    samples, and on the random stream and the ending. *)
Definition agree_upto (ops samples : nat) (E1 E2 : Env) : Prop :=
  (forall n, (n < ops)%nat -> outcome_of E1 n = outcome_of E2 n) /\
  (forall n, (n < ops)%nat -> cancelled_at E1 n = cancelled_at E2 n) /\
  (forall n, (n < samples)%nat -> sample_of E1 n = sample_of E2 n) /\
  (forall n, random_of E1 n = random_of E2 n) /\
  ends_at E1 = ends_at E2.

(** Whether an action consumes a journal entry at or beyond the given indices. *)
Definition consumes_beyond (ops samples : nat) (a : Action) : bool :=
  match a with
  | Sampled i _ => Nat.leb samples i
  | Delivered op _ _ | CancelDelivered op _ => Nat.leb ops op
  | _ => false
  end.

(** D9. The replay point: the longest prefix of a trace that consumes only the first [ops]
    operation results and the first [samples] samples. *)
Fixpoint cut (ops samples : nat) (tr : list Action) : list Action :=
  match tr with
  | [] => []
  | a :: rest => if consumes_beyond ops samples a then [] else a :: cut ops samples rest
  end.

(** Every arrival schedule a statement quantifies over is monotone (D7). *)
Definition schedules (A1 A2 : Arrival) : Prop := monotone A1 /\ monotone A2.

(** The trace with its ending removed: everything before the attempt-end turn. A suspension
    adds [Interrupted] actions and [Exited Suspended]; a crash adds [Exited Crashed]. *)
Definition ending_tail (tail : list Action) : Prop :=
  (exists hs, tail = map Interrupted hs ++ [Exited Suspended]) \/ tail = [Exited Crashed].

(** ** S1. Arrival independence *)

(** For any program and two environments with the same values and the same ending, the traces
    agree, whatever the two arrival schedules. Restrictions R1 to R3 hold by construction in
    the model (Model.v). *)
Definition S1 : Prop :=
  forall P E1 E2 A1 A2 n1 n2,
    same_values E1 E2 -> ends_at E1 = ends_at E2 -> schedules A1 A2 ->
    compatible (run P E1 A1 n1) (run P E2 A2 n2).

(** If the attempts end at different points, the traces agree up to the earlier end: a trace
    with an ending is, before its ending, compatible with the same attempt never ended. *)
Definition S1_end : Prop :=
  forall P E1 E2 A1 A2 n1 n2,
    same_values E1 E2 -> ends_at E2 = None -> schedules A1 A2 ->
    exists before tail,
      run P E1 A1 n1 = before ++ tail /\ (tail = [] \/ ending_tail tail) /\
      compatible before (run P E2 A2 n2).

(** ** S2. Replay determinism *)

(** A replay of a journal prefix (environments agreeing on the first [ops] results and the
    first [samples] samples) gives the same trace up to the replay point, whatever the arrival
    schedules: a live attempt, a replay, and a mixed attempt are all schedules. *)
Definition S2 : Prop :=
  forall P E1 E2 A1 A2 ops samples n1 n2,
    agree_upto ops samples E1 E2 -> schedules A1 A2 ->
    compatible (cut ops samples (run P E1 A1 n1)) (cut ops samples (run P E2 A2 n2)).

(** ** S3. Violations are trace events *)

(** A violation is at the same position in both traces, whatever the arrival schedules. The
    exception for resumes the executor did not issue is S5's environment, not this one. *)
Definition S3 : Prop :=
  forall P E A1 A2 n1 n2 i v,
    schedules A1 A2 ->
    nth_error (run P E A1 n1) i = Some (Violated v) ->
    (i < length (run P E A2 n2))%nat ->
    nth_error (run P E A2 n2) i = Some (Violated v).

(** ** S4. Single await *)

(** The handle of the fiber a command was issued for, if the action is a command. *)
Definition command_of (a : Action) : option (nat * nat) :=
  match a with
  | Command op h _ _ | SleepCommand op h _ => Some (op, h)
  | _ => None
  end.

(** Whether the action ends the wait for operation [op] of fiber [h]: its delivery, its
    cancellation, the fiber's interruption (abandonment), or the next link of its sleep chain. *)
Definition ends_wait (op h : nat) (a : Action) : bool :=
  match a with
  | Delivered op' _ _ | CancelDelivered op' _ => Nat.eqb op op'
  | Interrupted h' => Nat.eqb h h'
  | SleepCommand op' h' _ => Nat.eqb h h' && negb (Nat.eqb op op')
  | _ => false
  end.

(** After each command, no other fiber's command appears before the wait ends. *)
Fixpoint single_await (tr : list Action) : Prop :=
  match tr with
  | [] => True
  | a :: rest =>
      match command_of a with
      | Some (op, h) =>
          (forall pre b post, rest = pre ++ b :: post ->
             forallb (fun x => negb (ends_wait op h x)) pre = true ->
             forall op' h', command_of b = Some (op', h') -> h' = h)
          /\ single_await rest
      | None => single_await rest
      end
  end.

(** At most one durable operation is awaited, and a second is a violation whose command is
    never issued: in every trace, commands are single-awaited. *)
Definition S4 : Prop := forall P E A n, single_await (run P E A n).

(** ** S5. Resumes not issued by the executor are detected *)

(** In the extended environment, if a source outside Restate resumes a fiber waiting on it, the
    attempt records [StepOutsideTurn] and runs nothing more: the trace ends with the violation
    and the defect. This is S5 relative to E1, E2 and R2, which the model builds in. *)
Definition S5 : Prop :=
  forall P E A X n,
    In (Violated StepOutsideTurn) (run_with P E A X n) ->
    exists before, run_with P E A X n = before ++ [Violated StepOutsideTurn; Exited Defect].

(** And such a resume is never missed: if a fiber is waiting outside when the resume comes,
    the violation is recorded at that micro-step. *)
Definition S5_detects : Prop :=
  forall pol P E A X k h v f,
    let st := iterate pol P E A X k (initial P E) in
    finished st = None -> X (micro st) = Some (h, v) ->
    find_fiber h (fibers st) = Some f -> status f = WaitingOutside ->
    In (Violated StepOutsideTurn) (trace (step pol P E A X st)).

(** ** S6. Blocked means blocked forever *)

(** If the queue is empty, nothing is awaited, the root has not finished, and the attempt does
    not end here, the next step records the violation, under every arrival schedule. *)
Definition S6 : Prop :=
  forall P E A A' k,
    let st := iterate policy_v1 P E A no_outside_resumes k (initial P E) in
    finished st = None -> queue st = [] -> awaited st = None -> root_done st = false ->
    (forall n how, ends_at E = Some (n, how) -> n <> progress st) ->
    trace (step policy_v1 P E A' no_outside_resumes st)
      = trace st ++ [Violated BlockedWithNothingAwaited; Exited Defect].

(** ** S7. Delivery *)

(** If the awaited operation's result has arrived at a turn boundary, the next step delivers it:
    its sample command comes first. *)
Definition S7 : Prop :=
  forall P E A k aw,
    let st := iterate policy_v1 P E A no_outside_resumes k (initial P E) in
    finished st = None -> queue st = [] -> awaited st = Some aw ->
    A (awaited_op aw) (micro st) = true ->
    (forall n how, ends_at E = Some (n, how) -> n <> progress st) ->
    exists rest, trace (step policy_v1 P E A no_outside_resumes st)
      = trace st ++ SampleCommand (next_sample st) :: rest.

(** And a turn starts with a delivery, a cancellation or the attempt end, and nothing else: a
    step from an empty queue to a non-empty one adds a sample command or an interruption. *)
Definition S7_turns : Prop :=
  forall P E A k,
    let st := iterate policy_v1 P E A no_outside_resumes k (initial P E) in
    let st' := step policy_v1 P E A no_outside_resumes st in
    finished st = None -> queue st = [] -> queue st' <> [] ->
    exists a rest, trace st' = trace st ++ a :: rest /\
      ((exists i, a = SampleCommand i) \/ (exists h, a = Interrupted h)).

(** ** S8. Time rule *)

(** [L] never decreases from one micro-step to the next (P2). *)
Definition S8_monotone : Prop :=
  forall P E A k,
    let st := iterate policy_v1 P E A no_outside_resumes k (initial P E) in
    logical st <= logical (step policy_v1 P E A no_outside_resumes st).

(** After a completed sleep chunk, [L] has grown by at least the chunk (P3), and is at least
    the sample (P4); after anything else delivered or cancelled, it is at least the sample. *)
Definition S8_floor : Prop :=
  forall P E A k h op chunk rest,
    let st := iterate policy_v1 P E A no_outside_resumes k (initial P E) in
    let st' := step policy_v1 P E A no_outside_resumes st in
    finished st = None -> queue st = [] ->
    awaited st = Some (AwaitSleep h op chunk rest) -> cancelled_at E op = false ->
    A op (micro st) = true ->
    (forall n how, ends_at E = Some (n, how) -> n <> progress st) ->
    logical st' >= logical st + chunk /\
    logical st' >= sample_value (sample_of E (next_sample st)).

(** A cancelled sleep adds no floor (P8): [L] becomes the larger of [L] and the sample. *)
Definition S8_cancel : Prop :=
  forall P E A k h op chunk rest,
    let st := iterate policy_v1 P E A no_outside_resumes k (initial P E) in
    let st' := step policy_v1 P E A no_outside_resumes st in
    finished st = None -> queue st = [] ->
    awaited st = Some (AwaitSleep h op chunk rest) -> cancelled_at E op = true ->
    A op (micro st) = true ->
    (forall n how, ends_at E = Some (n, how) -> n <> progress st) ->
    logical st' = Z.max (logical st) (sample_value (sample_of E (next_sample st))).

(** Every durable sleep command is between 1 ms and [max_chunk] (P9). *)
Definition S8_chunks : Prop :=
  forall P E A n op h d, In (SleepCommand op h d) (run P E A n) -> 0 < d <= max_chunk.

(** The number of durable sleep commands in a trace. *)
Definition sleep_commands (tr : list Action) : nat :=
  length (filter (fun a => match a with SleepCommand _ _ _ => true | _ => false end) tr).

(** P5, corrected (the approved wording is refuted; see the dossier). [L] is at most the latest
    sample's true time plus the largest host error, plus [lead] for every sleep, when true time
    never decreases, every host error is at most [emax], and a timer fires at most [lead]
    before its chunk ends in true time. The lead adds up per sleep: [L] gains the whole chunk
    while true time may gain [lead] less. *)
Definition S8_upper : Prop :=
  forall P E A emax lead,
    (forall i j, (i <= j)%nat -> true_time (sample_of E i) <= true_time (sample_of E j)) ->
    (forall i, host_error (sample_of E i) <= emax) ->
    0 <= lead ->
    (forall k h op chunk rest,
       let st := iterate policy_v1 P E A no_outside_resumes k (initial P E) in
       awaited st = Some (AwaitSleep h op chunk rest) ->
       true_time (sample_of E (next_sample st))
         >= true_time (sample_of E (pred (next_sample st))) + chunk - lead) ->
    forall k,
      let st := iterate policy_v1 P E A no_outside_resumes k (initial P E) in
      logical st <= true_time (sample_of E (pred (next_sample st))) + emax
                    + Z.of_nat (sleep_commands (trace st)) * lead.

(** S8 is the conjunction. *)
Definition S8 : Prop :=
  S8_monotone /\ S8_floor /\ S8_cancel /\ S8_chunks /\ S8_upper.

(** ** S9. Single-fiber equivalence *)

(** A program with one fiber: no body forks. *)
CoInductive no_forks : itree FiberE unit -> Prop :=
| nf_ret r t : observe t = RetF r -> no_forks t
| nf_tau t u : observe t = TauF u -> no_forks u -> no_forks t
| nf_vis X (e : FiberE X) k t :
    observe t = VisF e k ->
    (match e with Fork _ _ => False | _ => True end) ->
    (forall x, no_forks (k x)) -> no_forks t.

Definition single_fiber (P : Program) : Prop :=
  no_forks (main (bodies P (root P))) /\ no_forks (finalizer (bodies P (root P))).

(** Neither executor reaches the two places where they differ: no sleep longer than
    [max_chunk], and never blocked with nothing awaited before the root finishes. *)
Definition in_common (P : Program) (E : Env) (A : Arrival) : Prop :=
  forall n op h d,
    In (SleepCommand op h d) (run_rev3 P E A n) -> d <= max_chunk.

Definition S9 : Prop :=
  forall P E A n,
    single_fiber P -> in_common P E A ->
    ~ In (Violated BlockedWithNothingAwaited) (run P E A n) ->
    run P E A n = run_rev3 P E A n.

(** ** S10. Random replay *)

Definition draws_of (tr : list Action) : list nat :=
  flat_map (fun a => match a with Drawn _ r => [r] | _ => [] end) tr.

Definition S10 : Prop :=
  forall P E A1 A2 n1 n2,
    schedules A1 A2 -> compatible (draws_of (run P E A1 n1)) (draws_of (run P E A2 n2)).

(** ** S11. Abandonment is silent *)

(** If operation [op] is abandoned in an attempt, changing its outcome or whether it is
    cancelled changes no trace. *)
Definition S11 : Prop :=
  forall P E1 E2 A k op,
    let st := iterate policy_v1 P E1 A no_outside_resumes k (initial P E1) in
    In op (abandoned st) ->
    (forall n, n <> op -> outcome_of E1 n = outcome_of E2 n) ->
    (forall n, n <> op -> cancelled_at E1 n = cancelled_at E2 n) ->
    (forall n, sample_of E1 n = sample_of E2 n) ->
    (forall n, random_of E1 n = random_of E2 n) ->
    ends_at E1 = ends_at E2 ->
    forall n, (n <= k)%nat -> run P E1 A n = run P E2 A n.
