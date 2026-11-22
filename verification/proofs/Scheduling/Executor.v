(** * The executor: the rest of D5, with D8 and D9.

    A deterministic micro-step function [step], and [run], which applies it a given number of
    times. Each micro-step either runs one task (the fiber at the head of the queue, until it
    blocks or takes [max_ops] operations), or, at a turn boundary (D8: the queue is empty),
    delivers the awaited result, waits for it, or ends the attempt. *)

From Coq Require Import List ZArith Bool Arith.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model.
Import ListNotations.
Open Scope Z_scope.

(** ** Helpers on state *)

Definition with_fibers (st : State) (fs : list Fiber) : State :=
  {| fibers := fs; queue := queue st; awaited := awaited st; abandoned := abandoned st;
     next_op := next_op st; next_sample := next_sample st; next_handle := next_handle st;
     draws := draws st; logical := logical st; memory := memory st; trace := trace st;
     micro := micro st; progress := progress st; finished := finished st |}.

(** One record update for the fields the executor changes together. *)
Definition update (st : State) (fs : list Fiber) (q : list nat) (aw : option Awaited)
    (ab : list nat) (op sm hd dr : nat) (l : Z) (tr : list Action) (fd : option Exit)
    : State :=
  {| fibers := fs; queue := q; awaited := aw; abandoned := ab; next_op := op;
     next_sample := sm; next_handle := hd; draws := dr; logical := l; memory := memory st;
     trace := tr; micro := micro st; progress := progress st; finished := fd |}.

Definition emit (st : State) (a : Action) : State :=
  update st (fibers st) (queue st) (awaited st) (abandoned st) (next_op st) (next_sample st)
    (next_handle st) (draws st) (logical st) (trace st ++ [a]) (finished st).

Definition finish (st : State) (e : Exit) : State :=
  let st' := emit st (Exited e) in
  update st' (fibers st') [] (awaited st') (abandoned st') (next_op st') (next_sample st')
    (next_handle st') (draws st') (logical st') (trace st') (Some e).

(** A violation is recorded and the attempt ends with a defect (rule 7: violations stick and
    interrupt the root; in the model nothing after it runs). *)
Definition violate (st : State) (v : Violation) : State :=
  finish (emit st (Violated v)) Defect.

Definition find_fiber (h : nat) (fs : list Fiber) : option Fiber :=
  find (fun f => Nat.eqb (handle f) h) fs.

Definition put_fiber (f : Fiber) (fs : list Fiber) : list Fiber :=
  map (fun g => if Nat.eqb (handle g) (handle f) then f else g) fs.

Definition set_code (f : Fiber) (c : itree FiberE unit) (p : Pending) (s : Status) : Fiber :=
  {| handle := handle f; code := c; fin := fin f; pending := p; status := s;
     interrupted := interrupted f |}.

Definition new_fiber (h : nat) (b : Body) : Fiber :=
  {| handle := h; code := main b; fin := finalizer b; pending := NoPending; status := Ready;
     interrupted := false |}.

(** Interrupting a fiber switches it to its finalizer. If it awaited the durable operation,
    that operation is abandoned: no delivery, no sample, no listener (D5). *)
Definition interrupt_fiber (st : State) (h : nat) : State :=
  match find_fiber h (fibers st) with
  | None => st
  | Some f =>
      match status f with
      | Done => st
      | _ =>
          let f' := {| handle := h; code := fin f; fin := Ret tt; pending := NoPending;
                       status := Ready; interrupted := true |} in
          let '(aw, ab) :=
            match awaited st with
            | Some (AwaitOp h' op) | Some (AwaitSleep h' op _ _) =>
                if Nat.eqb h' h then (None, op :: abandoned st) else (awaited st, abandoned st)
            | None => (None, abandoned st)
            end in
          let st' := emit st (Interrupted h) in
          update st' (put_fiber f' (fibers st')) (queue st' ++ [h]) aw ab (next_op st')
            (next_sample st') (next_handle st') (draws st') (logical st') (trace st')
            (finished st')
      end
  end.

(** ** Running one fiber *)

(** Runs fiber [f] for at most [ops] more operations, with [fuel] bounding nested immediate
    forks. Returns the new state; the fiber's own record is stored in it. *)
Fixpoint run_fiber (pol : Policy) (P : Program) (E : Env) (fuel ops : nat) (st : State) (f : Fiber)
    {struct fuel} : State :=
  match fuel with
  | O =>
      (* Fuel bounds nested immediate forks for Coq's termination check. Running out behaves
         as the scheduler's yield: the fiber is stored and queued again, never dropped. *)
      let st' := with_fibers st (put_fiber f (fibers st)) in
      update st' (fibers st') (queue st' ++ [handle f]) (awaited st') (abandoned st')
        (next_op st') (next_sample st') (next_handle st') (draws st') (logical st')
        (trace st') (finished st')
  | S fuel' =>
      match finished st with
      | Some _ => st
      | None =>
      match ops with
      | O =>
          (* The scheduler makes the fiber yield after [max_ops] operations. *)
          let st' := with_fibers st (put_fiber f (fibers st)) in
          update st' (fibers st') (queue st' ++ [handle f]) (awaited st') (abandoned st')
            (next_op st') (next_sample st') (next_handle st') (draws st') (logical st')
            (trace st') (finished st')
      | S ops' =>
      let h := handle f in
      match observe (code f) with
      | RetF _ =>
          with_fibers st (put_fiber (set_code f (Ret tt) NoPending Done) (fibers st))
      | TauF t => run_fiber pol P E fuel' ops' st (set_code f t NoPending Ready)
      | VisF e k =>
          match e in FiberE X return (X -> itree FiberE unit) -> State with
          | ReadClock => fun k =>
              let st' := emit st (ClockRead h (logical st)) in
              run_fiber pol P E fuel' ops' st' (set_code f (k (logical st)) NoPending Ready)
          | Draw => fun k =>
              let r := random_of E (draws st) in
              let st' := emit st (Drawn h r) in
              let st'' := update st' (fibers st') (queue st') (awaited st') (abandoned st')
                (next_op st') (next_sample st') (next_handle st') (S (draws st'))
                (logical st') (trace st') (finished st') in
              run_fiber pol P E fuel' ops' st'' (set_code f (k r) NoPending Ready)
          | Fork kind idx => fun k =>
              let child := new_fiber (next_handle st) (bodies P idx) in
              let parent := set_code f (k (next_handle st)) NoPending Ready in
              let st1 := update st (put_fiber parent (fibers st) ++ [child]) (queue st)
                (awaited st) (abandoned st) (next_op st) (next_sample st) (S (next_handle st))
                (draws st) (logical st) (trace st) (finished st) in
              match kind with
              | Queued =>
                  let st2 := update st1 (fibers st1) (queue st1 ++ [handle child])
                    (awaited st1) (abandoned st1) (next_op st1) (next_sample st1)
                    (next_handle st1) (draws st1) (logical st1) (trace st1) (finished st1) in
                  run_fiber pol P E fuel' ops' st2 parent
              | Immediate =>
                  (* The child runs nested until it blocks; then the parent continues. *)
                  let st2 := run_fiber pol P E fuel' max_ops st1 child in
                  match find_fiber h (fibers st2) with
                  | Some parent' => run_fiber pol P E fuel' ops' st2 parent'
                  | None => st2
                  end
              end
          | StartAwait kind args => fun k =>
              match awaited st with
              | Some _ => violate st SecondAwait
              | None =>
                  let op := next_op st in
                  let st' := emit st (Command op h kind args) in
                  update st' (put_fiber (set_code f (code f) (ResumeOutcome k) AwaitingDurable)
                    (fibers st')) (queue st') (Some (AwaitOp h op)) (abandoned st') (S op)
                    (next_sample st') (next_handle st') (draws st') (logical st') (trace st')
                    (finished st')
              end
          | Sleep d => fun k =>
              let yield_now :=
                let st' := with_fibers st
                  (put_fiber (set_code f (k tt) NoPending Ready) (fibers st)) in
                update st' (fibers st') (queue st' ++ [h]) (awaited st') (abandoned st')
                  (next_op st') (next_sample st') (next_handle st') (draws st')
                  (logical st') (trace st') (finished st') in
              let start_chain (chunk : Z) (rest : Chain) :=
                match awaited st with
                | Some _ => violate st SecondAwait
                | None =>
                    let op := next_op st in
                    let st' := emit st (SleepCommand op h chunk) in
                    update st' (put_fiber (set_code f (code f) (ResumeUnit k) AwaitingDurable)
                      (fibers st')) (queue st') (Some (AwaitSleep h op chunk rest))
                      (abandoned st') (S op) (next_sample st') (next_handle st') (draws st')
                      (logical st') (trace st') (finished st')
                end in
              let hang :=
                with_fibers st (put_fiber (set_code f (code f) NoPending Hung) (fibers st)) in
              if chunk_long_sleeps pol then
                match d with
                | Millis ms =>
                    if ms <=? 0 then yield_now
                    else if ms <=? max_chunk then start_chain ms NoChain
                    else start_chain max_chunk (Remaining (ms - max_chunk))
                | Forever => start_chain max_chunk Endless
                end
              else
                match d with
                | Millis ms =>
                    if ms <=? 0 then yield_now
                    else if ms <=? max_safe then start_chain ms NoChain
                    else hang
                | Forever => hang
                end
          | YieldNow => fun k =>
              let st' := with_fibers st
                (put_fiber (set_code f (k tt) NoPending Ready) (fibers st)) in
              update st' (fibers st') (queue st' ++ [h]) (awaited st') (abandoned st')
                (next_op st') (next_sample st') (next_handle st') (draws st') (logical st')
                (trace st') (finished st')
          | Interrupt target => fun k =>
              let st' := with_fibers st
                (put_fiber (set_code f (k tt) NoPending Ready) (fibers st)) in
              let st'' := interrupt_fiber st' target in
              match find_fiber h (fibers st'') with
              | Some f' => run_fiber pol P E fuel' ops' st'' f'
              | None => st''
              end
          | ReadRef r => fun k =>
              run_fiber pol P E fuel' ops' st (set_code f (k (memory st r)) NoPending Ready)
          | WriteRef r v => fun k =>
              let st' := {| fibers := fibers st; queue := queue st; awaited := awaited st;
                abandoned := abandoned st; next_op := next_op st; next_sample := next_sample st;
                next_handle := next_handle st; draws := draws st; logical := logical st;
                memory := fun x => if Nat.eqb x r then v else memory st x; trace := trace st;
                micro := micro st; progress := progress st; finished := finished st |} in
              run_fiber pol P E fuel' ops' st' (set_code f (k tt) NoPending Ready)
          | WaitOutside => fun k =>
              with_fibers st
                (put_fiber (set_code f (code f) (ResumeNat k) WaitingOutside) (fibers st))
          end k
      end
      end
      end
  end.

(** ** Delivery at a turn boundary *)

(** The sample taken at delivery, inside the turn (D5): its command, its value, and [L]. *)
Definition take_sample (E : Env) (st : State) (floor : Z) : State :=
  let i := next_sample st in
  let s := sample_value (sample_of E i) in
  let st1 := emit (emit st (SampleCommand i)) (Sampled i s) in
  update st1 (fibers st1) (queue st1) (awaited st1) (abandoned st1) (next_op st1) (S i)
    (next_handle st1) (draws st1) (next_logical (logical st1) floor s) (trace st1)
    (finished st1).

(** Resumes fiber [h] with its pending continuation, as the first task of the new turn. *)
Definition resume (st : State) (h : nat) (o : option Outcome) : State :=
  match find_fiber h (fibers st) with
  | None => st
  | Some f =>
      let c := match pending f, o with
               | ResumeOutcome k, Some v => k v
               | ResumeUnit k, _ => k tt
               | _, _ => code f
               end in
      update st (put_fiber (set_code f c NoPending Ready) (fibers st)) (h :: queue st) None
        (abandoned st) (next_op st) (next_sample st) (next_handle st) (draws st)
        (logical st) (trace st) (finished st)
  end.

(** Delivers the awaited operation's result, whose index is [op], once it has arrived. *)
Definition deliver (E : Env) (st : State) (aw : Awaited) : State :=
  match aw with
  | AwaitOp h op =>
      if cancelled_at E op then interrupt_fiber (emit (take_sample E st 0) (CancelDelivered op h)) h
      else
        let o := outcome_of E op in
        resume (emit (take_sample E st 0) (Delivered op h (Some o))) h (Some o)
  | AwaitSleep h op chunk rest =>
      if cancelled_at E op then interrupt_fiber (emit (take_sample E st 0) (CancelDelivered op h)) h
      else
        let st1 := take_sample E st chunk in
        let next (c : Z) (r : Chain) :=
          let op' := next_op st1 in
          let st2 := emit st1 (SleepCommand op' h c) in
          update st2 (fibers st2) (queue st2) (Some (AwaitSleep h op' c r)) (abandoned st2)
            (S op') (next_sample st2) (next_handle st2) (draws st2) (logical st2)
            (trace st2) (finished st2) in
        match rest with
        | NoChain => resume (emit st1 (Delivered op h None)) h None
        | Remaining d =>
            if d <=? max_chunk then next d NoChain
            else next max_chunk (Remaining (d - max_chunk))
        | Endless => next max_chunk Endless
        end
  end.

Definition awaited_op (aw : Awaited) : nat :=
  match aw with AwaitOp _ op | AwaitSleep _ op _ _ => op end.

Definition root_done (st : State) : bool :=
  match find_fiber 0%nat (fibers st) with
  | Some f => match status f with Done => true | _ => false end
  | None => false
  end.

(** ** The micro-step *)

Definition tick (st : State) (advanced : bool) : State :=
  {| fibers := fibers st; queue := queue st; awaited := awaited st; abandoned := abandoned st;
     next_op := next_op st; next_sample := next_sample st; next_handle := next_handle st;
     draws := draws st; logical := logical st; memory := memory st; trace := trace st;
     micro := S (micro st);
     progress := if advanced then S (progress st) else progress st;
     finished := finished st |}.

(** The attempt end (D5): a suspension interrupts every unfinished fiber as one turn and exits;
    a crash stops at once. *)
Definition end_attempt (st : State) (how : Ending) : State :=
  match how with
  | EndCrash => finish st Crashed
  | EndSuspend =>
      let live := filter (fun f => match status f with Done => false | _ => true end)
                    (fibers st) in
      finish (fold_left (fun s f => interrupt_fiber s (handle f)) live st) Suspended
  end.

Definition step (pol : Policy) (P : Program) (E : Env) (A : Arrival) (X : OutsideResumes) (st : State)
    : State :=
  match finished st with
  | Some _ => st
  | None =>
  match X (micro st) with
  | Some (h, _) =>
      match find_fiber h (fibers st) with
      | Some f => match status f with
                  | WaitingOutside => tick (violate st StepOutsideTurn) true
                  | _ => tick st false
                  end
      | None => tick st false
      end
  | None =>
  match ends_at E with
  | Some (n, how) => if Nat.eqb n (progress st) then tick (end_attempt st how) true
                     else
  match queue st with
  | h :: rest =>
      let st0 := update st (fibers st) rest (awaited st) (abandoned st) (next_op st)
        (next_sample st) (next_handle st) (draws st) (logical st) (trace st) (finished st) in
      match find_fiber h (fibers st0) with
      | Some f => tick (run_fiber pol P E max_ops max_ops st0 f) true
      | None => tick st0 true
      end
  | [] =>
      match awaited st with
      | Some aw => if A (awaited_op aw) (micro st) then tick (deliver E st aw) true
                   else tick st false
      | None => if root_done st then tick (finish st Succeeded) true
                else if blocked_is_violation pol then
                  tick (violate st BlockedWithNothingAwaited) true
                else tick st false
      end
  end
  | None =>
  match queue st with
  | h :: rest =>
      let st0 := update st (fibers st) rest (awaited st) (abandoned st) (next_op st)
        (next_sample st) (next_handle st) (draws st) (logical st) (trace st) (finished st) in
      match find_fiber h (fibers st0) with
      | Some f => tick (run_fiber pol P E max_ops max_ops st0 f) true
      | None => tick st0 true
      end
  | [] =>
      match awaited st with
      | Some aw => if A (awaited_op aw) (micro st) then tick (deliver E st aw) true
                   else tick st false
      | None => if root_done st then tick (finish st Succeeded) true
                else if blocked_is_violation pol then
                  tick (violate st BlockedWithNothingAwaited) true
                else tick st false
      end
  end
  end
  end
  end.

(** The state at attempt start: the root fiber (handle 0) queued, and [L] set from the first
    journaled sample. *)
Definition initial (P : Program) (E : Env) : State :=
  let s := sample_value (sample_of E 0) in
  {| fibers := [new_fiber 0%nat (bodies P (root P))]; queue := [0%nat]; awaited := None;
     abandoned := []; next_op := 0%nat; next_sample := 1%nat; next_handle := 1%nat;
     draws := 0%nat; logical := s; memory := fun _ => 0%nat;
     trace := [SampleCommand 0%nat; Sampled 0%nat s];
     micro := 0%nat; progress := 0%nat; finished := None |}.

Fixpoint iterate (pol : Policy) (P : Program) (E : Env) (A : Arrival) (X : OutsideResumes) (n : nat)
    (st : State) : State :=
  match n with
  | O => st
  | S n' => iterate pol P E A X n' (step pol P E A X st)
  end.

(** The trace after [n] micro-steps (a finite prefix of the attempt, D6). *)
Definition run (P : Program) (E : Env) (A : Arrival) (n : nat) : list Action :=
  trace (iterate policy_v1 P E A no_outside_resumes n (initial P E)).

(** Revision 3's executor, for S9. *)
Definition run_rev3 (P : Program) (E : Env) (A : Arrival) (n : nat) : list Action :=
  trace (iterate policy_rev3 P E A no_outside_resumes n (initial P E)).

(** The same, with resumes from outside Restate (for S5). *)
Definition run_with (P : Program) (E : Env) (A : Arrival) (X : OutsideResumes) (n : nat)
    : list Action :=
  trace (iterate policy_v1 P E A X n (initial P E)).
