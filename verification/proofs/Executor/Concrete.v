(** * A simple concrete runtime, one instance of the interface (#37).

    It exists for the non-vacuity witnesses. Fibers run a small first-order language with
    finalizers, masks, queued and immediate forks, shared cells, priorities, and interruption
    that waits for the target's exit, as Effect's [Fiber.interrupt] does (#34). *)

From Coq Require Import List ZArith Bool Arith.
From Durable Require Import Runtime.
Import ListNotations.
Open Scope nat_scope.

(** ** The fiber language *)

(** [CFork true] is an immediate fork, run nested inside the forking step; [CFork false]
    queues the child's first step. [CYield p] queues the fiber with priority [p]. [CAwaitCell]
    blocks until the cell is non-zero, as a [Deferred] does. [CInterrupt] requests the
    target's interruption and waits until the target has exited. [CMaskOn] and [CMaskOff]
    open and close an [uninterruptible] region. *)
Inductive Code :=
| CEnd (v : nat)
| CFail (v : nat)
| CClock (k : Z -> Code)
| CDraw (k : nat -> Code)
| CStart (op : Op) (k : Outcome -> Code)
| CFork (immediate : bool) (body : nat) (k : FiberId -> Code)
| CYield (priority : nat) (k : Code)
| CWrite (cell v : nat) (k : Code)
| CRead (cell : nat) (k : nat -> Code)
| CAwaitCell (cell : nat) (k : nat -> Code)
| CInterrupt (target : FiberId) (k : Code)
| CMaskOn (k : Code)
| CMaskOff (k : Code).

(** A body is its main code and the finalizer that runs when it exits, however it exits. *)
Record Body := { main : Code; fin : Code }.

Record CProg := { bodies : nat -> Body; root_body : nat }.

(** ** Runtime state *)

Inductive Status :=
| Ready
| Await (tok : Token)
| OnCell (cell : nat)
| OnExit (target : FiberId)
| Finished.

(** [kout] resumes an await, [knat] a cell wait. [exit] is how the fiber will exit once its
    finalizer has run. [unwinding] means the finalizer is running. *)
Record Fiber := {
  fid : FiberId;
  code : Code;
  kout : Outcome -> Code;
  knat : nat -> Code;
  final : Code;
  mask : nat;
  status : Status;
  intr : bool;
  unwinding : bool;
  queued : bool;
  begun : bool;
  exit : RootExit
}.

Record CState := {
  program : CProg;
  fibers : list Fiber;
  cells : nat -> nat;
  next_fid : nat;
  next_tok : nat
}.

(** ** Helpers *)

Definition dummy_out : Outcome -> Code := fun _ => CEnd 0.
Definition dummy_nat : nat -> Code := fun _ => CEnd 0.

Definition new_fiber (f : FiberId) (b : Body) : Fiber :=
  {| fid := f; code := main b; kout := dummy_out; knat := dummy_nat; final := fin b;
     mask := 0; status := Ready; intr := false; unwinding := false; queued := false;
     begun := false; exit := ExitSuccess 0 |}.

Definition with_code (f : Fiber) (c : Code) (s : Status) : Fiber :=
  {| fid := fid f; code := c; kout := kout f; knat := knat f; final := final f;
     mask := mask f; status := s; intr := intr f; unwinding := unwinding f;
     queued := queued f; begun := begun f; exit := exit f |}.

Definition with_flags (f : Fiber) (m : nat) (i u q b : bool) (e : RootExit) : Fiber :=
  {| fid := fid f; code := code f; kout := kout f; knat := knat f; final := final f;
     mask := m; status := status f; intr := i; unwinding := u; queued := q; begun := b;
     exit := e |}.

Definition with_konts (f : Fiber) (ko : Outcome -> Code) (kn : nat -> Code) : Fiber :=
  {| fid := fid f; code := code f; kout := ko; knat := kn; final := final f;
     mask := mask f; status := status f; intr := intr f; unwinding := unwinding f;
     queued := queued f; begun := begun f; exit := exit f |}.

Definition set_queued (f : Fiber) (q : bool) : Fiber :=
  with_flags f (mask f) (intr f) (unwinding f) q (begun f) (exit f).

Definition find (f : FiberId) (s : CState) : option Fiber :=
  find (fun g => Nat.eqb (fid g) f) (fibers s).

Definition put (g : Fiber) (s : CState) : CState :=
  {| program := program s;
     fibers := if existsb (fun h => Nat.eqb (fid h) (fid g)) (fibers s)
               then map (fun h => if Nat.eqb (fid h) (fid g) then g else h) (fibers s)
               else fibers s ++ [g];
     cells := cells s; next_fid := next_fid s; next_tok := next_tok s |}.

Definition set_cell (s : CState) (c v : nat) : CState :=
  {| program := program s; fibers := fibers s;
     cells := fun c' => if Nat.eqb c c' then v else cells s c';
     next_fid := next_fid s; next_tok := next_tok s |}.

Definition bump_fid (s : CState) : CState :=
  {| program := program s; fibers := fibers s; cells := cells s;
     next_fid := S (next_fid s); next_tok := next_tok s |}.

Definition bump_tok (s : CState) : CState :=
  {| program := program s; fibers := fibers s; cells := cells s;
     next_fid := next_fid s; next_tok := S (next_tok s) |}.

(** Script sequencing. *)
Fixpoint sbind {A B} (s : Script A) (k : A -> Script B) : Script B :=
  match s with
  | Done a => k a
  | Emit e s' => Emit e (sbind s' k)
  | AskClock f g => AskClock f (fun l => sbind (g l) k)
  | AskDraw f g => AskDraw f (fun r => sbind (g r) k)
  | Register f g => Register f (fun b => sbind (g b) k)
  end.

(** Queue fiber [g] if it is not queued already, reporting the task. *)
Definition enqueue (s : CState) (g : Fiber) (p : nat) : Script CState :=
  if queued g then Done s else Emit (EvQueue p (fid g)) (Done (put (set_queued g true) s)).

(** Wake every fiber waiting on a cell that is now non-zero, or on a fiber that has exited:
    each is made ready with its continuation and queued. *)
Fixpoint wake (s : CState) (gs : list Fiber) (pick : Fiber -> option Code) : Script CState :=
  match gs with
  | [] => Done s
  | g :: rest =>
      match pick g with
      | Some c => sbind (enqueue s (with_code g c Ready) 0) (fun s' => wake s' rest pick)
      | None => wake s rest pick
      end
  end.

Definition wake_cell (s : CState) (c v : nat) : Script CState :=
  wake s (fibers s) (fun g => match status g with
                              | OnCell c' => if Nat.eqb c c' then Some (knat g v) else None
                              | _ => None end).

Definition wake_exit (s : CState) (f : FiberId) : Script CState :=
  wake s (fibers s) (fun g => match status g with
                              | OnExit t => if Nat.eqb t f then Some (code g) else None
                              | _ => None end).

(** Operations a fiber runs before it yields, as Effect's [MaxOpsBeforeYield]. *)
Definition max_ops : nat := 2048.

(** Start unwinding: the finalizer becomes the code, and the exit is recorded. A fiber
    whose finalizer is already running is not unwound again: a cancellation or defect
    delivered to its finalizer ends the fiber, as a defect in an Effect finalizer does. *)
Definition unwind (g : Fiber) (e : RootExit) : Fiber :=
  if unwinding g then with_code (with_flags g 0 false true (queued g) (begun g) e) (CEnd 0) Ready
  else with_code (with_flags g 0 false true (queued g) (begun g) e) (final g) Ready.

(** ** Running a fiber *)

(** [go fuel ops s g] runs fiber [g] until it blocks, exits, yields, or has run [max_ops]
    operations. The fuel bounds the whole task; when it runs out the fiber is queued again. *)
Fixpoint go (fuel ops : nat) (s : CState) (g : Fiber) : Script CState :=
  match fuel with
  | O => enqueue (put g s) g 0
  | S fuel' =>
  if (max_ops <=? ops) then enqueue (put g s) g 0 else
  if intr g && Nat.eqb (mask g) 0 && negb (unwinding g)
  then go fuel' (S ops) s (unwind g ExitInterrupted) else
  let cont := fun c => go fuel' (S ops) s (with_code g c Ready) in
  let finish_main := fun e => go fuel' (S ops) s (unwind g e) in
  match code g with
  | CEnd v | CFail v =>
      if unwinding g then
        let g' := with_code g (CEnd v) Finished in
        let s' := put g' s in
        let exits := Emit (EvFiberExited (fid g)) (Done s') in
        let rooted := if Nat.eqb (fid g) 0 then Emit (EvFiberExited 0)
                        (Emit (EvRootExit (exit g)) (Done s')) else exits in
        sbind rooted (fun s'' => wake_exit s'' (fid g))
      else finish_main (match code g with CFail _ => ExitFailure v | _ => ExitSuccess v end)
  | CClock k => AskClock (fid g) (fun l => go fuel' (S ops) s (with_code g (k l) Ready))
  | CDraw k => AskDraw (fid g) (fun r => go fuel' (S ops) s (with_code g (k r) Ready))
  | CStart op k =>
      let tok := next_tok s in
      Emit (EvStart (fid g) tok op)
        (Done (put (with_konts (with_code g (CEnd 0) (Await tok)) k dummy_nat) (bump_tok s)))
  | CFork imm b k =>
      let child := new_fiber (next_fid s) (bodies (program s) b) in
      let s1 := bump_fid s in
      let parent := with_code g (k (fid child)) Ready in
      if imm then
        Register (fid child) (fun i =>
          let child' := with_flags child 0 i false false true (exit child) in
          sbind (go fuel' 0 (put parent s1) child')
             (fun s2 => match find (fid g) s2 with
                        | Some p => go fuel' (S ops) s2 p
                        | None => Done s2 end))
      else sbind (enqueue (put child s1) child 0) (fun s2 => go fuel' (S ops) s2 parent)
  | CYield p k => enqueue (put (with_code g k Ready) s) (with_code g k Ready) p
  | CWrite c v k =>
      let s1 := put (with_code g k Ready) (set_cell s c v) in
      sbind (if Nat.eqb v 0 then Done s1 else wake_cell s1 c v)
        (fun s2 => match find (fid g) s2 with
                   | Some p => go fuel' (S ops) s2 p
                   | None => Done s2 end)
  | CRead c k => cont (k (cells s c))
  | CAwaitCell c k =>
      if Nat.eqb (cells s c) 0
      then Done (put (with_konts (with_code g (CEnd 0) (OnCell c)) dummy_out k) s)
      else cont (k (cells s c))
  | CInterrupt t k =>
      let waiting := with_code g k (OnExit t) in
      sbind (interrupt fuel' (put waiting s) t)
        (fun s2 => match find (fid g) s2, find t s2 with
                   | Some p, Some tg =>
                       match status tg, status p with
                       | Finished, OnExit _ => go fuel' (S ops) s2 (with_code p (code p) Ready)
                       | _, _ => Done s2
                       end
                   | Some p, None => go fuel' (S ops) s2 (with_code p (code p) Ready)
                   | None, _ => Done s2
                   end)
  | CMaskOn k => go fuel' (S ops) s (with_flags (with_code g k Ready) (S (mask g)) (intr g)
                   (unwinding g) (queued g) (begun g) (exit g))
  | CMaskOff k => go fuel' (S ops) s (with_flags (with_code g k Ready) (pred (mask g))
                   (intr g) (unwinding g) (queued g) (begun g) (exit g))
  end
  end

(** Request fiber [t]'s interruption. A masked fiber only records it. An unmasked fiber that
    awaits a durable operation reports the release before its finalizer runs (I4); a blocked
    one unwinds at once; a ready one unwinds when it next runs. *)
with interrupt (fuel : nat) (s : CState) (t : FiberId) : Script CState :=
  match fuel with
  | O => Done s
  | S fuel' =>
  match find t s with
  | None => Done s
  | Some g =>
      if unwinding g then Done s else
      match status g with
      | Finished => Done s
      | _ =>
      if negb (Nat.eqb (mask g) 0) then
        Done (put (with_flags g (mask g) true (unwinding g) (queued g) (begun g) (exit g)) s)
      else
      match status g with
      | Await tok => Emit (EvRelease t tok) (go fuel' 0 s (unwind g ExitInterrupted))
      | OnCell _ | OnExit _ => go fuel' 0 s (unwind g ExitInterrupted)
      | _ =>
          Done (put (with_flags g (mask g) true (unwinding g) (queued g) (begun g) (exit g)) s)
      end
      end
  end
  end.

(** ** Tasks *)

Definition task_fuel : nat := 4000.

Definition start_fiber (s : CState) (g : Fiber) : Script CState :=
  if begun g then go task_fuel 0 s g
  else Register (fid g) (fun i =>
         let g' := with_flags g (mask g) (intr g || i) (unwinding g) false true (exit g) in
         go task_fuel 0 (put g' s) g').

Definition c_run_task (s : CState) (t : Task) : Script CState :=
  match t with
  | StartRoot =>
      match find 0 s with
      | Some _ => Done s
      | None =>
          let g := new_fiber 0 (bodies (program s) (root_body (program s))) in
          start_fiber (put g s) g
      end
  | RunQueued f =>
      match find f s with
      | Some g => match status g with
                  | Ready => if queued g then start_fiber s (set_queued g false) else Done s
                  | _ => Done s
                  end
      | None => Done s
      end
  | Deliver f tok o =>
      match find f s with
      | Some g => match status g with
                  | Await tok' => if Nat.eqb tok tok'
                                  then go task_fuel 0 s (with_code g (kout g o) Ready)
                                  else Done s
                  | _ => Done s
                  end
      | None => Done s
      end
  | DeliverCancel f tok | DeliverDefect f tok =>
      let e := match t with DeliverDefect _ _ => ExitDefect | _ => ExitInterrupted end in
      match find f s with
      | Some g => match status g with
                  | Await tok' => if Nat.eqb tok tok'
                                  then Emit (EvRelease f tok) (go task_fuel 0 s (unwind g e))
                                  else Done s
                  | _ => Done s
                  end
      | None => Done s
      end
  | RequestInterrupt f => interrupt task_fuel s f
  end.

Definition c_init (p : CProg) (_ : nat) : CState :=
  {| program := p; fibers := []; cells := fun _ => 0; next_fid := 1; next_tok := 0 |}.

(** The concrete runtime. Its equivalence is equality. *)
Definition concrete : Runtime :=
  {| rstate := CState; prog := CProg; requiv := eq; init := c_init; run_task := c_run_task |}.
