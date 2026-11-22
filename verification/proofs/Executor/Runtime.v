(** * The runtime interface of #37, revision 9.

    The fiber runtime is a parameter of the proofs. A runtime is a state, an equivalence on
    states, an initial state for a program and seed, and a function that runs one task. Running
    a task gives a [Script]: a finite tree of the executor's events, whose branches take the
    executor's answers to clock reads and draws, ending in the runtime's next state.

    This file is the owner's interface (proof-dossier, section 7). It holds definitions and
    named propositions, and no proofs. *)

From Coq Require Import List ZArith Bool Arith.
Import ListNotations.
Open Scope Z_scope.

(** ** Identities *)

(** A fiber's lifetime identity (I7), an await token, and the name of a task the runtime
    queued. All three are allocated by the runtime from its own state. *)
Definition FiberId := nat.
Definition Token := nat.
Definition TaskId := nat.

(** ** Durable operations *)

(** A sleep's duration in whole milliseconds, or [Forever]. A fractional duration is rounded
    up before it reaches the model. *)
Inductive Duration := Millis (d : Z) | Forever.

(** A durable operation: a [run] step or call, with its kind and arguments kept abstract, or a
    sleep. *)
Inductive Op := ORun (kind : nat) (args : nat) | OSleep (d : Duration).

(** What a durable operation returns to the fiber awaiting it. A sleep returns [Value 0]. A
    cancellation is not an outcome: it is delivered as its own task. *)
Inductive Outcome := Value (v : nat) | Failure (v : nat).

(** The root's exit, as the runtime reports it once, after the root's cleanup (I6). *)
Inductive RootExit :=
| ExitSuccess (v : nat)
| ExitFailure (v : nat)
| ExitInterrupted
| ExitDefect.

(** ** Tasks and events *)

(** The tasks the executor asks the runtime to run. [DeliverDefect] refuses a durable
    operation started during closing (X6.3). *)
Inductive Task :=
| StartRoot
| RunQueued (t : TaskId)
| Deliver (f : FiberId) (tok : Token) (o : Outcome)
| DeliverCancel (f : FiberId) (tok : Token)
| DeliverDefect (f : FiberId) (tok : Token)
| RequestInterrupt (f : FiberId).

(** The events a task reports. [EvStart] starts a durable operation for a fiber, which then
    awaits the token. [EvRelease] reports that a fiber actually unwound out of an await or out
    of waiting for the slot (I4). [EvQueue] queues a task with a priority. *)
Inductive Event :=
| EvStart (f : FiberId) (tok : Token) (op : Op)
| EvRelease (f : FiberId) (tok : Token)
| EvQueue (priority : nat) (t : TaskId)
| EvFiberExited (f : FiberId)
| EvRootExit (e : RootExit).

(** A task's run: a finite tree. [AskClock] is answered with [L] and [AskDraw] with the next
    value of the seeded stream; both name the fiber that asks. [Register] reports a fiber's
    first run, before its first step (I8); the executor answers whether to interrupt it
    before that step, which it does for every fiber that registers during closing (X6.3), as
    the adapter's creation hook calls [interruptUnsafe] at registration. The tree is inductive, so every
    task returns: I9 holds by construction in the model, and whether Effect's tasks return is
    a question for the conformance suite. *)
Inductive Script (S : Type) :=
| Done (s : S)
| Emit (e : Event) (k : Script S)
| AskClock (f : FiberId) (k : Z -> Script S)
| AskDraw (f : FiberId) (k : nat -> Script S)
| Register (f : FiberId) (k : bool -> Script S).

Arguments Done {S} s.
Arguments Emit {S} e k.
Arguments AskClock {S} f k.
Arguments AskDraw {S} f k.
Arguments Register {S} f k.

(** ** Runtimes *)

(** [prog] is the runtime's type of programs. [init] takes the program and the seed. *)
Record Runtime := {
  rstate : Type;
  prog : Type;
  requiv : rstate -> rstate -> Prop;
  init : prog -> nat -> rstate;
  run_task : rstate -> Task -> Script rstate
}.

(** ** Logs: a runtime driven by a sequence of tasks *)

(** A runtime's log interleaves the tasks it was given, the events it reported and the
    answers it received. *)
Inductive LogEntry :=
| LTask (t : Task)
| LEvent (e : Event)
| LClock (f : FiberId) (l : Z)
| LDraw (f : FiberId) (r : nat)
| LRegister (f : FiberId) (interrupted : bool).

(** Answers for clock reads and draws, by their position among the reads of each kind. *)
Record Answers := { clock_answer : nat -> Z; draw_answer : nat -> nat;
                    register_answer : FiberId -> bool }.

(** Running one script against the answers, from read counters [c] and [d]. *)
Fixpoint play {X} (A : Answers) (c d : nat) (s : Script X)
    : list LogEntry * X * nat * nat :=
  match s with
  | Done x => ([], x, c, d)
  | Emit e k =>
      let '(log, x, c', d') := play A c d k in (LEvent e :: log, x, c', d')
  | AskClock f k =>
      let l := clock_answer A c in
      let '(log, x, c', d') := play A (S c) d (k l) in (LClock f l :: log, x, c', d')
  | AskDraw f k =>
      let r := draw_answer A d in
      let '(log, x, c', d') := play A c (S d) (k r) in (LDraw f r :: log, x, c', d')
  | Register f k =>
      let b := register_answer A f in
      let '(log, x, c', d') := play A c d (k b) in (LRegister f b :: log, x, c', d')
  end.

(** Running a sequence of tasks from state [s]. *)
Fixpoint drive (R : Runtime) (A : Answers) (c d : nat) (s : rstate R) (ts : list Task)
    : list LogEntry * rstate R :=
  match ts with
  | [] => ([], s)
  | t :: rest =>
      let '(log, s', c', d') := play A c d (run_task R s t) in
      let '(log', s'') := drive R A c' d' s' rest in
      (LTask t :: log ++ log', s'')
  end.

(** The fiber an entry is attributed to, if any. Queueing a task is attributed to no fiber. *)
Definition entry_fiber (e : LogEntry) : option FiberId :=
  match e with
  | LEvent (EvStart f _ _) | LEvent (EvRelease f _) | LRegister f _
  | LEvent (EvFiberExited f) | LClock f _ | LDraw f _ => Some f
  | _ => None
  end.

(** ** Script equivalence *)

(** Two scripts are related when they report the same events and ask the same questions in
    the same order, and end in states related by [eqv] for every sequence of answers. *)
Inductive script_rel {S} (eqv : S -> S -> Prop) : Script S -> Script S -> Prop :=
| rel_done : forall x y, eqv x y -> script_rel eqv (Done x) (Done y)
| rel_emit : forall e k1 k2,
    script_rel eqv k1 k2 -> script_rel eqv (Emit e k1) (Emit e k2)
| rel_clock : forall f k1 k2,
    (forall l, script_rel eqv (k1 l) (k2 l)) -> script_rel eqv (AskClock f k1) (AskClock f k2)
| rel_draw : forall f k1 k2,
    (forall r, script_rel eqv (k1 r) (k2 r)) -> script_rel eqv (AskDraw f k1) (AskDraw f k2)
| rel_register : forall f k1 k2,
    (forall b, script_rel eqv (k1 b) (k2 b)) -> script_rel eqv (Register f k1) (Register f k2).

(** ** The interface properties *)

(** Each property of #37's interface table is either a named proposition here, which the
    statements take as a hypothesis, or holds by construction in this model. The dossier's
    table says which, and why.

    - I1, determinism: by the proposition [I1] below. A Coq runtime is a function, so equal
      states give equal scripts; the equivalence makes the property the one the conformance
      suite tests, where Effect's states in two processes are equivalent but not equal.
    - I2, closed world: by construction. A script reaches the outside only through [Event],
      [AskClock] and [AskDraw].
    - I3, guarded entry: by construction. A foreign resume or interruption is an input of the
      executor, which never passes it to [run_task], so the runtime's state is unchanged.
    - I4, release at unwind: by the proposition [I4].
    - I5, visible pending work: not stated. No statement here depends on it. It is what makes
      S6's violation correct for Effect: work hidden in the runtime would make a blocked
      verdict false, and only the conformance suite can check that.
    - I6, exit reporting: by the proposition [I6] for "at most once"; a second report is also
      a violation the executor checks. "After cleanup" is not stated, for the reason of I5.
    - I7, lifetime identities: by the proposition [I7]; that identities depend only on the
      state follows from [I1].
    - I8, fiber registry: by the proposition [I8].
    - I9, finite tasks: by construction, since [Script] is inductive. *)

(** I1. [requiv] is an equivalence, and from equivalent states a task gives related scripts.
    Attempts in different processes start from states equivalent to [init], which the
    statements that use I1 take as a hypothesis. *)
Definition I1 (R : Runtime) : Prop :=
  (forall s, requiv R s s) /\
  (forall s1 s2, requiv R s1 s2 -> requiv R s2 s1) /\
  (forall s1 s2 s3, requiv R s1 s2 -> requiv R s2 s3 -> requiv R s1 s3) /\
  (forall s1 s2 t, requiv R s1 s2 -> script_rel (requiv R) (run_task R s1 t) (run_task R s2 t)).

(** Whether a log entry ends fiber [f]'s await of token [tok]: a delivery of its result, a
    cancellation or a defect for it, or a release report. *)
Definition ends_await (f : FiberId) (tok : Token) (e : LogEntry) : bool :=
  match e with
  | LTask (Deliver f' tok' _) | LTask (DeliverCancel f' tok') | LTask (DeliverDefect f' tok')
  | LEvent (EvRelease f' tok') => Nat.eqb f f' && Nat.eqb tok tok'
  | _ => false
  end.

(** No entry attributed to [f] occurs before the first entry of [log] that ends the await. *)
Fixpoint quiet_until_end (f : FiberId) (tok : Token) (log : list LogEntry) : Prop :=
  match log with
  | [] => True
  | e :: rest =>
      if ends_await f tok e then True
      else entry_fiber e <> Some f /\ quiet_until_end f tok rest
  end.

(** I4. From any reachable state, a fiber that starts a durable operation does nothing more
    until the await ends: by a delivery, a cancellation, a defect, or its own release report.
    So the release is reported before the fiber's cleanup runs, which is the part of I4 the
    executor relies on. That a masked fiber does not unwind is the runtime's own behaviour,
    tested by the conformance suite. *)
(** The tokens of the durable operations a log reports started. *)
Definition start_tokens (log : list LogEntry) : list Token :=
  flat_map (fun e => match e with LEvent (EvStart _ tok _) => [tok] | _ => [] end) log.

(** I4 also says each await is identified by its token, which the model states as: no token
    is started twice within an attempt. *)
Definition I4 (R : Runtime) : Prop :=
  (forall p seed A ts pre f tok op post,
     fst (drive R A 0 0 (init R p seed) ts) = pre ++ LEvent (EvStart f tok op) :: post ->
     quiet_until_end f tok post) /\
  (forall p seed A ts, NoDup (start_tokens (fst (drive R A 0 0 (init R p seed) ts)))).

(** The number of root exit reports in a log. *)
Definition root_exits (log : list LogEntry) : nat :=
  length (filter (fun e => match e with LEvent (EvRootExit _) => true | _ => false end) log).

(** The first fiber a log registers: the root, when the log starts with [StartRoot]. *)
Fixpoint first_registered (log : list LogEntry) : option FiberId :=
  match log with
  | [] => None
  | LRegister f _ :: _ => Some f
  | _ :: rest => first_registered rest
  end.

(** I6, the part stated here: the root's exit is reported at most once, and only after the
    root has exited, which the log shows as the exit report of the first fiber registered.
    #37's "after its cleanup", together with I8's "removed after it exits", requires the
    second half; without it a runtime could leave the root registered, and every verdict
    would be [VDefect] (step 3 review of the rev3 domain). *)
Definition I6 (R : Runtime) : Prop :=
  forall p seed A ts,
    let log := fst (drive R A 0 0 (init R p seed) ts) in
    (root_exits log <= 1)%nat /\
    (forall pre e post, log = pre ++ LEvent (EvRootExit e) :: post ->
       exists r, first_registered pre = Some r /\ In (LEvent (EvFiberExited r)) pre).

(** The fibers whose start a log reports, in order. *)
Definition started (log : list LogEntry) : list FiberId :=
  flat_map (fun e => match e with LRegister f _ => [f] | _ => [] end) log.

(** I7. No identity is reported started twice within an attempt. *)
Definition I7 (R : Runtime) : Prop :=
  forall p seed A ts, NoDup (started (fst (drive R A 0 0 (init R p seed) ts))).

(** I8. Every entry attributed to a fiber comes after that fiber's start report, and none
    comes after its exit report. *)
Definition I8 (R : Runtime) : Prop :=
  forall p seed A ts pre e post f,
    fst (drive R A 0 0 (init R p seed) ts) = pre ++ e :: post ->
    entry_fiber e = Some f ->
    (exists b, e = LRegister f b \/ In (LRegister f b) pre) /\
    ~ In (LEvent (EvFiberExited f)) pre.

(** A runtime that meets the interface, as far as the model states it. *)
Definition Meets (R : Runtime) : Prop := I1 R /\ I4 R /\ I6 R /\ I7 R /\ I8 R.
