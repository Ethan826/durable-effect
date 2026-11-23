(** * The executor model X1 to X6 of #37, revision 9.

    One executor per attempt, written as a total function so that it can be extracted. Its
    state is first-order; the runtime's state is kept beside it, never inside it. The owner's
    interface: definitions only, no proofs. *)

From Coq Require Import List ZArith Bool Arith.
From Durable Require Import Runtime.
Import ListNotations.
Open Scope Z_scope.

(** ** Constants *)

(** The longest single durable sleep; a longer sleep is a chain of links. *)
Definition max_chunk : Z := 2147483647.

(** The largest integer JavaScript represents exactly. An [L] above it is a violation (P6). *)
Definition max_safe : Z := 9007199254740991.

(** ** X1. The journal and the inputs *)

(** A command the executor issues: a durable operation (for a sleep, the link's chunk) or a
    clock sample. *)
Inductive CmdKind := KOp (op : Op) | KSample.

(** What a notification carries. A sample's notification carries the reading, or a terminal
    failure. A transient failure of a sample ends the attempt as the SDK does, which the model
    treats as an [Ended] cut. *)
Inductive Result := ROutcome (o : Outcome) | RSample (s : Z) | RSampleTerminal.

(** The exogenous journal entries: a notification for the command numbered [c], or the
    invocation's cancel signal. *)
Inductive JIn := InNotify (c : nat) (r : Result) | InCancel.

(** Inputs from outside Restate. [FResumeToken] is a resume for a token the executor did not
    issue, and [FQueueOutside] a task queued outside any slice; the implementation link uses
    both to test the executor's runtime checks. *)
Inductive Foreign :=
| FResume (f : FiberId)
| FInterrupt (f : FiberId)
| FResumeToken (tok : Token)
| FQueueOutside (t : TaskId).

(** The three kinds of cut (X3). *)
Inductive Cut := Suspended | Ended | Crashed.

(** An attempt's inputs. [entries] is the order Restate persisted the exogenous entries in.
    [persisted] lists the commands already in the journal, which a replay must reissue.
    [foreign n] is the foreign input that arrives when [n] steps have done something (see
    [progress]). [stream] is
    the random stream seeded with the invocation id, and [seed] the runtime's seed. *)
Record Inputs := {
  entries : list JIn;
  persisted : list CmdKind;
  foreign : nat -> option Foreign;
  stream : nat -> nat;
  seed : nat
}.

(** What differs between two attempts with the same inputs. [arrived i] is how many entries
    have arrived by micro-step [i]; a replay has them all from the start. [cut_at] is the
    [progress] at which a cut happens, and [stop_at] the [progress] at which the next attempt
    starts in the same process, which stops a closing after a cut. *)
Record Schedule := {
  arrived : nat -> nat;
  cut_at : option (nat * Cut);
  stop_at : option nat
}.

(** ** The trace *)

Inductive Violation :=
| SecondOp | Blocked | ForeignResume | ForeignInterrupt | Priority
| ResumeUnawaited | SecondExit | Overflow | SampleTerminal.

Inductive Verdict := VRoot (e : RootExit) | VDefect | VMismatch.

(** What a handler can observe, in order, with three additions the statements need. A
    command records the fiber and token it was issued for, if any; an applied sample records
    [L] after it and the sleep link it credits, if any; and [AStart] records a fiber starting
    a durable operation. The journal holds only each command's kind and each sample's
    reading. [ACut] marks where an attempt was cut. [ARegister] records a fiber's first
    run, so that S9 can count fibers: a fiber can register and leave the registry within
    one task, where no other record shows it (step 3 review of the rev3 domain). *)
Inductive Action :=
| ARegister (f : FiberId)
| AStart (f : FiberId) (tok : Token) (op : Op)
| ACommand (c : nat) (k : CmdKind) (owner : option (FiberId * Token))
| ASampled (c : nat) (s : Z) (l : Z) (credit : option (FiberId * Token * Z))
| ADelivered (f : FiberId) (tok : Token) (o : Outcome)
| ACancelled (f : FiberId) (tok : Token)
| ARefused (f : FiberId) (tok : Token)
| AClock (f : FiberId) (l : Z)
| ADraw (f : FiberId) (r : nat)
| AViolation (v : Violation)
| ACut (k : Cut)
| AExit (v : Verdict).

(** ** Executor state *)

(** What remains of a sleep after its current link. *)
Inductive Chain := NoChain | Remaining (d : Z) | Endless.

(** What a sample follows: the initial sample, a result for an awaiting fiber, a sleep link,
    a cancelled operation, or an operation whose fiber [f] unwound while its sample was
    pending. The last case cannot be reached, since nothing runs between a turn's end and the
    sample's application; if it were, the sample is retired unapplied, as the design's time
    rule says of a released operation (L unchanged, no sample taken). *)
Inductive Follows :=
| FInitial
| FResult (f : FiberId) (tok : Token) (o : Outcome)
| FLink (f : FiberId) (tok : Token) (chunk : Z) (rest : Chain)
| FCancelled (f : FiberId) (tok : Token)
| FReleased (f : FiberId) (tok : Token) (floor : Z).

(** The subscription: an operation awaited by a fiber, a sample, or a released operation. *)
Inductive Sub :=
| SOp (c : nat) (f : FiberId) (tok : Token) (op : Op) (chunk : Z) (rest : Chain)
| SSample (c : nat) (after : Follows)
| SReleased (c : nat).

Definition sub_cmd (s : Sub) : nat :=
  match s with SOp c _ _ _ _ _ | SSample c _ | SReleased c => c end.

Inductive Phase := POpen | PClosing (cut : option Cut) | PDone.

(** [awaiter] is the one fiber awaiting a durable operation or waiting for the slot (S4).
    [waiter] is the fiber waiting for the slot and the operation it asked for. [held] is a
    held cancellation (X5). [live] is the registry (I8). [progress] counts the steps that did
    something: a task, an entry consumed, a local turn or the end of closing. It does not
    count a step that waits, so it does not depend on when entries arrive, and foreign inputs
    and cuts are placed by it. [fseen] is the last [progress] at which a foreign input was
    taken. *)
Record XState := {
  phase : Phase;
  queue : list Task;
  sub : option Sub;
  awaiter : option (FiberId * Token);
  waiter : option (FiberId * Token * Op);
  held : bool;
  logical : Z;
  next_cmd : nat;
  cursor : nat;
  draws : nat;
  live : list FiberId;
  root_exit : option RootExit;
  violated : bool;
  trace : list Action;
  progress : nat;
  micro : nat;
  fseen : option nat
}.

(** ** Field updates *)

Definition mk p q s aw w h l nc cu d lv re v tr pr mi fs : XState :=
  {| phase := p; queue := q; sub := s; awaiter := aw; waiter := w; held := h; logical := l;
     next_cmd := nc; cursor := cu; draws := d; live := lv; root_exit := re; violated := v;
     trace := tr; progress := pr; micro := mi; fseen := fs |}.

Definition set_phase x v := mk v (queue x) (sub x) (awaiter x) (waiter x) (held x)
  (logical x) (next_cmd x) (cursor x) (draws x) (live x) (root_exit x) (violated x)
  (trace x) (progress x) (micro x) (fseen x).
Definition set_queue x v := mk (phase x) v (sub x) (awaiter x) (waiter x) (held x)
  (logical x) (next_cmd x) (cursor x) (draws x) (live x) (root_exit x) (violated x)
  (trace x) (progress x) (micro x) (fseen x).
Definition set_sub x v := mk (phase x) (queue x) v (awaiter x) (waiter x) (held x)
  (logical x) (next_cmd x) (cursor x) (draws x) (live x) (root_exit x) (violated x)
  (trace x) (progress x) (micro x) (fseen x).
Definition set_awaiter x v := mk (phase x) (queue x) (sub x) v (waiter x) (held x)
  (logical x) (next_cmd x) (cursor x) (draws x) (live x) (root_exit x) (violated x)
  (trace x) (progress x) (micro x) (fseen x).
Definition set_waiter x v := mk (phase x) (queue x) (sub x) (awaiter x) v (held x)
  (logical x) (next_cmd x) (cursor x) (draws x) (live x) (root_exit x) (violated x)
  (trace x) (progress x) (micro x) (fseen x).
Definition set_held x v := mk (phase x) (queue x) (sub x) (awaiter x) (waiter x) v
  (logical x) (next_cmd x) (cursor x) (draws x) (live x) (root_exit x) (violated x)
  (trace x) (progress x) (micro x) (fseen x).
Definition set_logical x v := mk (phase x) (queue x) (sub x) (awaiter x) (waiter x) (held x)
  v (next_cmd x) (cursor x) (draws x) (live x) (root_exit x) (violated x)
  (trace x) (progress x) (micro x) (fseen x).
Definition set_next_cmd x v := mk (phase x) (queue x) (sub x) (awaiter x) (waiter x) (held x)
  (logical x) v (cursor x) (draws x) (live x) (root_exit x) (violated x)
  (trace x) (progress x) (micro x) (fseen x).
Definition set_cursor x v := mk (phase x) (queue x) (sub x) (awaiter x) (waiter x) (held x)
  (logical x) (next_cmd x) v (draws x) (live x) (root_exit x) (violated x)
  (trace x) (progress x) (micro x) (fseen x).
Definition set_draws x v := mk (phase x) (queue x) (sub x) (awaiter x) (waiter x) (held x)
  (logical x) (next_cmd x) (cursor x) v (live x) (root_exit x) (violated x)
  (trace x) (progress x) (micro x) (fseen x).
Definition set_live x v := mk (phase x) (queue x) (sub x) (awaiter x) (waiter x) (held x)
  (logical x) (next_cmd x) (cursor x) (draws x) v (root_exit x) (violated x)
  (trace x) (progress x) (micro x) (fseen x).
Definition set_root_exit x v := mk (phase x) (queue x) (sub x) (awaiter x) (waiter x)
  (held x) (logical x) (next_cmd x) (cursor x) (draws x) (live x) v (violated x)
  (trace x) (progress x) (micro x) (fseen x).
Definition set_violated x v := mk (phase x) (queue x) (sub x) (awaiter x) (waiter x)
  (held x) (logical x) (next_cmd x) (cursor x) (draws x) (live x) (root_exit x) v
  (trace x) (progress x) (micro x) (fseen x).
Definition set_progress x v := mk (phase x) (queue x) (sub x) (awaiter x) (waiter x)
  (held x) (logical x) (next_cmd x) (cursor x) (draws x) (live x) (root_exit x)
  (violated x) (trace x) v (micro x) (fseen x).
Definition set_micro x v := mk (phase x) (queue x) (sub x) (awaiter x) (waiter x)
  (held x) (logical x) (next_cmd x) (cursor x) (draws x) (live x) (root_exit x)
  (violated x) (trace x) (progress x) v (fseen x).
Definition set_fseen x v := mk (phase x) (queue x) (sub x) (awaiter x) (waiter x)
  (held x) (logical x) (next_cmd x) (cursor x) (draws x) (live x) (root_exit x)
  (violated x) (trace x) (progress x) (micro x) v.

Definition emit (x : XState) (a : Action) : XState :=
  mk (phase x) (queue x) (sub x) (awaiter x) (waiter x) (held x) (logical x) (next_cmd x)
    (cursor x) (draws x) (live x) (root_exit x) (violated x) (trace x ++ [a]) (progress x)
    (micro x) (fseen x).

Definition enqueue (x : XState) (t : Task) : XState := set_queue x (queue x ++ [t]).

(** ** Equality on commands *)

Definition duration_eqb (a b : Duration) : bool :=
  match a, b with
  | Millis x, Millis y => Z.eqb x y
  | Forever, Forever => true
  | _, _ => false
  end.

Definition op_eqb (a b : Op) : bool :=
  match a, b with
  | ORun k1 a1, ORun k2 a2 => Nat.eqb k1 k2 && Nat.eqb a1 a2
  | OSleep d1, OSleep d2 => duration_eqb d1 d2
  | _, _ => false
  end.

(** What Restate compares when a replay reissues a command: its kind and name, here a run's
    [kind], but not a run's arguments or a sleep's duration (#37, the link table). *)
Definition cmd_eqb (a b : CmdKind) : bool :=
  match a, b with
  | KOp (ORun k1 _), KOp (ORun k2 _) => Nat.eqb k1 k2
  | KOp (OSleep _), KOp (OSleep _) => true
  | KSample, KSample => true
  | _, _ => false
  end.

Definition pair_eqb (a b : FiberId * Token) : bool :=
  Nat.eqb (fst a) (fst b) && Nat.eqb (snd a) (snd b).

(** ** X6. Violations and closing *)

(** A task that hands a result or a cancellation to a fiber; closing drops these (X6.1). *)
Definition is_delivery (t : Task) : bool :=
  match t with Deliver _ _ _ | DeliverCancel _ _ => true | _ => false end.

(** Closing: latch, retire the subscription without a sample, and request the interruption
    of every live fiber before any other queued task. A closing already under way, or one
    after a cut, only records the cut. *)
Definition close (x : XState) (cut : option Cut) : XState :=
  match phase x with
  | POpen =>
      let x1 := set_sub (set_waiter (set_awaiter (set_held x false) None) None) None in
      let q := map RequestInterrupt (live x) ++ filter (fun t => negb (is_delivery t)) (queue x)
      in set_queue (set_phase x1 (PClosing cut)) q
  | PClosing None => match cut with Some _ => set_phase x (PClosing cut) | None => x end
  | _ => x
  end.

(** Record the first violation and close (X6). A later violation is not recorded; the
    verdict is already [VDefect]. *)
Definition violate (x : XState) (v : Violation) : XState :=
  if violated x then x else close (set_violated (emit x (AViolation v)) true) None.

(** The verdict once closing has emptied the queue (X6.4). *)
Definition verdict (x : XState) : Verdict :=
  if violated x then VDefect
  else match root_exit x, live x with
       | Some e, [] => VRoot e
       | _, _ => VDefect
       end.

Definition finish (x : XState) (v : Verdict) : XState := set_phase (emit x (AExit v)) PDone.

(** ** Issuing commands *)

(** Issue a command, checked against the persisted journal: a replay that would issue a
    different command at a persisted index fails with a journal mismatch (S2). *)
Definition issue (I : Inputs) (x : XState) (k : CmdKind) (owner : option (FiberId * Token))
    (s : nat -> Sub) : XState :=
  let c := next_cmd x in
  let go := set_sub (set_next_cmd (emit x (ACommand c k owner)) (S c)) (Some (s c)) in
  match nth_error (persisted I) c with
  | Some k' => if cmd_eqb k k' then go else finish x VMismatch
  | None => go
  end.

Definition issue_sample (I : Inputs) (x : XState) (after : Follows) : XState :=
  issue I x KSample None (fun c => SSample c after).

(** A sleep's first link, or the next one: its chunk and what remains after it. *)
Definition split (d : Z) : Z * Chain :=
  if d <=? max_chunk then (d, NoChain) else (max_chunk, Remaining (d - max_chunk)).

Definition link_of (rest : Chain) : option (Z * Chain) :=
  match rest with
  | NoChain => None
  | Remaining d => Some (split d)
  | Endless => Some (max_chunk, Endless)
  end.

(** Issue the command for fiber [f]'s operation. A sleep's command is its first link. *)
Definition issue_op (I : Inputs) (x : XState) (f : FiberId) (tok : Token) (op : Op)
    : XState :=
  match op with
  | ORun _ _ => issue I x (KOp op) (Some (f, tok)) (fun c => SOp c f tok op 0 NoChain)
  | OSleep d =>
      let '(chunk, rest) := match d with Millis m => split m | Forever => (max_chunk, Endless)
                            end in
      issue I x (KOp (OSleep (Millis chunk))) (Some (f, tok))
        (fun c => SOp c f tok op chunk rest)
  end.

(** ** X5. Starting an operation, and releases *)

Definition zero_sleep (op : Op) : bool :=
  match op with OSleep (Millis d) => d <=? 0 | _ => false end.

(** Whether the slot is held without a fiber awaiting: by a released operation, the initial
    sample, or a sample whose fiber unwound. *)
Definition slot_held (x : XState) : bool :=
  match sub x with
  | Some (SReleased _) | Some (SSample _ FInitial) | Some (SSample _ (FReleased _ _ _)) => true
  | _ => false
  end.

(** A fiber starts a durable operation (S4, X5, X6.3). *)
Definition on_start (I : Inputs) (x : XState) (f : FiberId) (tok : Token) (op : Op)
    : XState :=
  match phase x with
  | PDone => x
  | PClosing _ => enqueue (emit x (AStart f tok op)) (DeliverDefect f tok)
  | POpen =>
      let x := emit x (AStart f tok op) in
      if zero_sleep op then enqueue x (Deliver f tok (Value 0))
      else match awaiter x with
           | Some _ => violate x SecondOp
           | None =>
               let x1 := set_awaiter x (Some (f, tok)) in
               if held x then enqueue (set_held x1 false) (DeliverCancel f tok)
               else if slot_held x then set_waiter x1 (Some (f, tok, op))
               else issue_op I x1 f tok op
           end
  end.

(** The fiber awaiting the subscription, if any, and the subscription it becomes once that
    fiber has unwound. *)
Definition release_sub (s : Sub) : option (FiberId * Token * Sub) :=
  match s with
  | SOp c f tok _ _ _ => Some (f, tok, SReleased c)
  | SSample c (FResult f tok _) | SSample c (FCancelled f tok) =>
      Some (f, tok, SSample c (FReleased f tok 0))
  | SSample c (FLink f tok k _) => Some (f, tok, SSample c (FReleased f tok k))
  | _ => None
  end.

Definition for_token (f : FiberId) (tok : Token) (t : Task) : bool :=
  match t with
  | Deliver f' tok' _ | DeliverCancel f' tok' => Nat.eqb f f' && Nat.eqb tok tok'
  | _ => false
  end.

(** A fiber reports that it unwound out of an await (I4). Any delivery still queued for that
    await is dropped, including a 0 ms sleep's. A dropped cancellation is held again, so it
    goes to the next fiber that starts a durable operation (X5; the combined review's F1
    found it lost). The executor otherwise ignores a release for an
    await it has already delivered, and every release during closing. *)
Definition on_release (x : XState) (f : FiberId) (tok : Token) : XState :=
  let dropped_cancel := existsb (fun t => match t with
                                          | DeliverCancel f' tok' => Nat.eqb f f' && Nat.eqb tok tok'
                                          | _ => false end) (queue x) in
  let x := match phase x with
           | POpen =>
               let x1 := set_queue x (filter (fun t => negb (for_token f tok t)) (queue x)) in
               if dropped_cancel then set_held x1 true else x1
           | _ => x
           end in
  match phase x, awaiter x with
  | POpen, Some a =>
      if negb (pair_eqb a (f, tok)) then x
      else
        let x1 := set_awaiter x None in
        match waiter x with
        | Some _ => set_waiter x1 None
        | None =>
            match sub x with
            | Some s => match release_sub s with
                        | Some (f', tok', s') =>
                            if pair_eqb (f', tok') (f, tok) then set_sub x1 (Some s') else x1
                        | None => x1
                        end
            | None => x1
            end
        end
  | _, _ => x
  end.

(** ** Events reported by a task *)

Definition remove_fiber (f : FiberId) (l : list FiberId) : list FiberId :=
  filter (fun g => negb (Nat.eqb f g)) l.

Definition on_event (I : Inputs) (x : XState) (e : Event) : XState :=
  match phase x with
  | PDone => x
  | _ =>
  match e with
  | EvStart f tok op => on_start I x f tok op
  | EvRelease f tok => on_release x f tok
  | EvQueue p t => if Nat.eqb p 0 then enqueue x (RunQueued t) else violate x Priority
  | EvFiberExited f => set_live x (remove_fiber f (live x))
  | EvRootExit r =>
      match root_exit x with
      | Some _ => violate x SecondExit
      | None => close (set_root_exit x (Some r)) None
      end
  end
  end.

(** Running a task's script: clock reads are answered with [L], draws from the stream. *)
Fixpoint interp {X} (I : Inputs) (x : XState) (s : Script X) : XState * X :=
  match s with
  | Done r => (x, r)
  | Emit e k => interp I (on_event I x e) k
  | AskClock f k =>
      let l := logical x in
      let x1 := match phase x with PDone => x | _ => emit x (AClock f l) end in
      interp I x1 (k l)
  | AskDraw f k =>
      let r := stream I (draws x) in
      let x1 := match phase x with
                | PDone => x
                | _ => emit (set_draws x (S (draws x))) (ADraw f r)
                end in
      interp I x1 (k r)
  | Register f k =>
      let closing := match phase x with PClosing _ => true | _ => false end in
      let x1 := match phase x with PDone => x | _ => emit x (ARegister f) end in
      interp I (set_live x1 (live x1 ++ [f])) (k closing)
  end.

(** What the trace records when a task hands something to a fiber. *)
Definition task_action (t : Task) : option Action :=
  match t with
  | Deliver f tok o => Some (ADelivered f tok o)
  | DeliverCancel f tok => Some (ACancelled f tok)
  | DeliverDefect f tok => Some (ARefused f tok)
  | _ => None
  end.

(** ** X2. Samples and notifications *)

(** Apply a sample's reading: the time rule, with the link's chunk credited, and the check
    against [max_safe] (P6). The initial sample sets [L]. *)
Definition apply_sample (x : XState) (c : nat) (s : Z) (after : Follows) : XState :=
  let credit := match after with
                | FLink f tok k _ => if 0 <? k then Some (f, tok, k) else None
                | _ => None
                end in
  let floor := match credit with Some (_, _, k) => k | None => 0 end in
  let l := match after with FInitial => s | _ => Z.max (logical x + floor) s end in
  if max_safe <? l then violate x Overflow
  else set_sub (set_logical (emit x (ASampled c s l credit)) l) None.

(** What follows an applied sample. *)
Definition after_sample (I : Inputs) (x : XState) (after : Follows) : XState :=
  match after with
  | FInitial => enqueue x StartRoot
  | FResult f tok o => enqueue x (Deliver f tok o)
  | FCancelled f tok => enqueue x (DeliverCancel f tok)
  | FLink f tok _ rest =>
      match link_of rest with
      | None => enqueue x (Deliver f tok (Value 0))
      | Some (chunk, rest') =>
          issue I x (KOp (OSleep (Millis chunk))) (Some (f, tok))
            (fun c => SOp c f tok (OSleep (Millis chunk)) chunk rest')
      end
  | FReleased _ _ _ => x
  end.

(** The subscription's notification. *)
Definition on_notify (I : Inputs) (x : XState) (s : Sub) (r : Result) : XState :=
  match s, r with
  | SOp _ f tok (OSleep _) k rest, ROutcome _ => issue_sample I x (FLink f tok k rest)
  | SOp _ f tok _ _ _, ROutcome o => issue_sample I x (FResult f tok o)
  | SSample _ (FReleased _ _ _), _ => set_sub x None
  | SSample c after, RSample v =>
      let x1 := apply_sample x c v after in
      match phase x1 with POpen => after_sample I x1 after | _ => x1 end
  | SSample _ _, RSampleTerminal => violate x SampleTerminal
  | SReleased _, _ => set_sub x None
  | _, _ => x
  end.

(** The cancel signal, observed through the subscription. *)
Definition on_cancel (I : Inputs) (x : XState) (s : Sub) : XState :=
  match s with
  | SOp _ f tok _ _ _ => issue_sample I x (FCancelled f tok)
  | SSample _ FInitial => issue_sample I (set_held x true) FInitial
  | SSample _ (FResult f tok _) | SSample _ (FLink f tok _ _) | SSample _ (FCancelled f tok) =>
      issue_sample I x (FCancelled f tok)
  | SSample _ (FReleased _ _ _) | SReleased _ => set_held (set_sub x None) true
  end.

(** The earliest arrived entry at the cursor, at a turn boundary with a subscription (X1). A
    notification for a retired command is consumed and ignored; one for a command not yet
    issued waits. *)
Definition at_boundary_sub (I : Inputs) (Sch : Schedule) (x : XState) (s : Sub)
    : option XState :=
  if (arrived Sch (micro x) <=? cursor x)%nat then None
  else match nth_error (entries I) (cursor x) with
       | None => None
       | Some InCancel => Some (on_cancel I (set_cursor x (S (cursor x))) s)
       | Some (InNotify c r) =>
           if Nat.eqb c (sub_cmd s) then Some (on_notify I (set_cursor x (S (cursor x))) s r)
           else if (c <? next_cmd x)%nat then Some (set_cursor x (S (cursor x)))
           else None
       end.

(** A turn boundary: the queue is empty (S6). [None] means the executor waits. *)
Definition at_boundary (I : Inputs) (Sch : Schedule) (x : XState) : option XState :=
  match phase x with
  | PDone => None
  | PClosing _ => Some (finish x (verdict x))
  | POpen =>
      match held x, waiter x with
      | true, Some (f, tok, _) =>
          Some (enqueue (set_waiter (set_held x false) None) (DeliverCancel f tok))
      | _, _ =>
      match sub x with
      | Some s => at_boundary_sub I Sch x s
      | None =>
          match waiter x with
          | Some (f, tok, op) => Some (issue_op I (set_waiter x None) f tok op)
          | None => Some (violate x Blocked)
          end
      end
      end
  end.

(** ** One step *)

(** The system: the executor's state and the runtime's, kept apart. *)
Record Sys (R : Runtime) := { xs : XState; rs : rstate R }.
Arguments xs {R} s.
Arguments rs {R} s.

(** A foreign input reaches the guard; the runtime is never called (I3). *)
Definition on_foreign (x : XState) (fi : Foreign) : XState :=
  match fi with
  | FResume _ => violate x ForeignResume
  | FInterrupt _ => violate x ForeignInterrupt
  | FResumeToken _ => violate x ResumeUnawaited
  | FQueueOutside _ => x
  end.

(** A cut (X3). A crash ends everything; any other cut closes the attempt. *)
Definition on_cut (x : XState) (k : Cut) : XState :=
  let x1 := emit x (ACut k) in
  match k with
  | Crashed => set_phase x1 PDone
  | _ => close x1 (Some k)
  end.

Definition cut_due (Sch : Schedule) (x : XState) : option Cut :=
  match cut_at Sch, phase x with
  | Some (n, k), POpen | Some (n, k), PClosing None =>
      if Nat.eqb n (progress x) then Some k else None
  | _, _ => None
  end.

Definition stop_due (Sch : Schedule) (x : XState) : bool :=
  match stop_at Sch, phase x with
  | Some n, PClosing (Some _) => (n <=? progress x)%nat
  | _, _ => false
  end.

Definition foreign_due (I : Inputs) (x : XState) : option Foreign :=
  match fseen x with
  | Some n => if Nat.eqb n (progress x) then None else foreign I (progress x)
  | None => foreign I (progress x)
  end.

(** Run the task at the head of the queue. *)
Definition run_head (R : Runtime) (I : Inputs) (x : XState) (r : rstate R) (t : Task)
    (rest : list Task) : XState * rstate R :=
  let x0 := set_progress (set_queue x rest) (S (progress x)) in
  let x1 := match task_action t with Some a => emit x0 a | None => x0 end in
  let x2 := match t, awaiter x1 with
            | Deliver f tok _, Some a | DeliverCancel f tok, Some a =>
                if pair_eqb a (f, tok) then set_awaiter x1 None else x1
            | _, _ => x1
            end in
  interp I x2 (run_task R r t).

Definition step (R : Runtime) (I : Inputs) (Sch : Schedule) (s : Sys R) : Sys R :=
  let x := xs s in
  let r := rs s in
  let next := fun x' r' => {| xs := set_micro x' (S (micro x)); rs := r' |} in
  match phase x with
  | PDone => s
  | _ =>
    if stop_due Sch x then next (set_phase x PDone) r else
    match foreign_due I x with
    | Some fi => next (on_foreign (set_fseen x (Some (progress x))) fi) r
    | None =>
    match cut_due Sch x with
    | Some k => next (on_cut x k) r
    | None =>
    match queue x with
    | t :: rest => let '(x', r') := run_head R I x r t rest in next x' r'
    | [] => match at_boundary I Sch x with
            | Some x' => next (set_progress x' (S (progress x))) r
            | None => next x r
            end
    end
    end
    end
  end.

(** ** Attempts *)

(** Attempt start: the initial sample is issued and becomes the subscription; the root starts
    once it is applied (X2). *)
Definition initial (R : Runtime) (p : prog R) (I : Inputs) : Sys R :=
  let x0 := mk POpen [] None None None false 0 0 0 0 [] None false [] 0 0 None in
  {| xs := issue_sample I x0 FInitial; rs := init R p (seed I) |}.

Fixpoint iterate (R : Runtime) (I : Inputs) (Sch : Schedule) (n : nat) (s : Sys R) : Sys R :=
  match n with
  | O => s
  | S m => iterate R I Sch m (step R I Sch s)
  end.

(** The trace after [n] micro-steps. *)
Definition run (R : Runtime) (p : prog R) (I : Inputs) (Sch : Schedule) (n : nat)
    : list Action :=
  trace (xs (iterate R I Sch n (initial R p I))).

(** A replay: every entry has arrived from the start. *)
Definition replayed (I : Inputs) : nat -> nat := fun _ => length (entries I).
