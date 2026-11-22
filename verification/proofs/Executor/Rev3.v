(** * Revision 3's executor, for S9.

    Written from revision 3's design text, separately from [Exec]: it shares only the types of
    the trace, and a review checks the two against each other (#37, S9). Revision 3 had one
    awaited operation and the root-fiber rule. It sampled the clock at attempt start and at
    every delivery, sent a sleep of up to 2^53 - 1 ms whole and never sent a longer one, made
    a cancellation during a sample a defect, and hung when the handler blocked. It queued
    tasks in Effect's order, which is queue order when no task has a priority other than 0. *)

From Coq Require Import List ZArith Bool Arith.
From Durable Require Import Runtime Exec.
Import ListNotations.
Open Scope Z_scope.

(** The awaited command: an operation for a fiber with its floor, or a sample followed by a
    delivery or a cancellation, or the initial sample. *)
Inductive Then3 := TInitial | TDeliver (f : FiberId) (tok : Token) (o : Outcome) (floor : Z)
                 | TCancel (f : FiberId) (tok : Token).

Inductive Await3 :=
| WOp (c : nat) (f : FiberId) (tok : Token) (floor : Z)
| WSample (c : nat) (next : Then3).

Record R3 := {
  q3 : list Task;
  aw3 : option Await3;
  l3 : Z;
  cmd3 : nat;
  cur3 : nat;
  draws3 : nat;
  tr3 : list Action;
  done3 : bool;
  micro3 : nat
}.

Definition mk3 q a l c cu d t dn m : R3 :=
  {| q3 := q; aw3 := a; l3 := l; cmd3 := c; cur3 := cu; draws3 := d; tr3 := t; done3 := dn;
     micro3 := m |}.

Definition emit3 (x : R3) (a : Action) : R3 :=
  mk3 (q3 x) (aw3 x) (l3 x) (cmd3 x) (cur3 x) (draws3 x) (tr3 x ++ [a]) (done3 x) (micro3 x).

Definition push3 (x : R3) (t : Task) : R3 :=
  mk3 (q3 x ++ [t]) (aw3 x) (l3 x) (cmd3 x) (cur3 x) (draws3 x) (tr3 x) (done3 x) (micro3 x).

Definition await3 (x : R3) (a : option Await3) : R3 :=
  mk3 (q3 x) a (l3 x) (cmd3 x) (cur3 x) (draws3 x) (tr3 x) (done3 x) (micro3 x).

Definition end3 (x : R3) (v : Verdict) : R3 :=
  let y := emit3 x (AExit v) in
  mk3 (q3 y) (aw3 y) (l3 y) (cmd3 y) (cur3 y) (draws3 y) (tr3 y) true (micro3 y).

(** Issue a command and await it. *)
Definition cmd (x : R3) (k : CmdKind) (owner : option (FiberId * Token)) (a : nat -> Await3)
    : R3 :=
  let c := cmd3 x in
  let y := emit3 x (ACommand c k owner) in
  mk3 (q3 y) (Some (a c)) (l3 y) (S c) (cur3 y) (draws3 y) (tr3 y) (done3 y) (micro3 y).

Definition sample3 (x : R3) (n : Then3) : R3 := cmd x KSample None (fun c => WSample c n).

(** A fiber starts a durable operation. A sleep of [d <= 0] is not sent and the fiber
    yields; a sleep above 2^53 - 1 ms, or an infinite one, is never sent, so the fiber hangs. *)
Definition start3 (x : R3) (f : FiberId) (tok : Token) (op : Op) : R3 :=
  let x := emit3 x (AStart f tok op) in
  match aw3 x with
  | Some _ => end3 (emit3 x (AViolation SecondOp)) VDefect
  | None =>
      match op with
      | OSleep (Millis d) =>
          if d <=? 0 then push3 x (Deliver f tok (Value 0))
          else if max_safe <? d then x
          else cmd x (KOp op) (Some (f, tok)) (fun c => WOp c f tok d)
      | OSleep Forever => x
      | ORun _ _ => cmd x (KOp op) (Some (f, tok)) (fun c => WOp c f tok 0)
      end
  end.

Definition event3 (x : R3) (e : Event) : R3 :=
  if done3 x then x else
  match e with
  | EvStart f tok op => start3 x f tok op
  | EvQueue _ t => push3 x (RunQueued t)
  | EvRootExit r => end3 x (VRoot r)
  | _ => x
  end.

Fixpoint interp3 {X} (I : Inputs) (x : R3) (s : Script X) : R3 * X :=
  match s with
  | Done r => (x, r)
  | Emit e k => interp3 I (event3 x e) k
  | AskClock f k => interp3 I (if done3 x then x else emit3 x (AClock f (l3 x))) (k (l3 x))
  | AskDraw f k =>
      let r := stream I (draws3 x) in
      let y := if done3 x then x
               else mk3 (q3 x) (aw3 x) (l3 x) (cmd3 x) (cur3 x) (S (draws3 x))
                      (tr3 x ++ [ADraw f r]) false (micro3 x) in
      interp3 I y (k r)
  | Register _ k => interp3 I x (k false)
  end.

(** The awaited command's entry, when it has arrived. *)
Definition entry3 (I : Inputs) (Sch : Schedule) (x : R3) (a : Await3) : R3 :=
  if (arrived Sch (micro3 x) <=? cur3 x)%nat then x else
  let y := mk3 (q3 x) (aw3 x) (l3 x) (cmd3 x) (S (cur3 x)) (draws3 x) (tr3 x) (done3 x)
             (micro3 x) in
  match nth_error (entries I) (cur3 x), a with
  | Some InCancel, WOp _ f tok _ => sample3 y (TCancel f tok)
  | Some InCancel, WSample _ _ => end3 y VDefect
  | Some (InNotify c (ROutcome o)), WOp c' f tok floor =>
      if Nat.eqb c c' then sample3 y (TDeliver f tok o floor) else y
  | Some (InNotify c (RSample s)), WSample c' n =>
      if Nat.eqb c c' then
        let floor := match n with TDeliver _ _ _ k => k | _ => 0 end in
        let credit := match n with
                      | TDeliver f tok _ k => if 0 <? k then Some (f, tok, k) else None
                      | _ => None end in
        let l := match n with TInitial => s | _ => Z.max (l3 y + floor) s end in
        let z := mk3 (q3 y) None l (cmd3 y) (cur3 y) (draws3 y)
                   (tr3 y ++ [ASampled c s l credit]) false (micro3 y) in
        match n with
        | TInitial => push3 z StartRoot
        | TDeliver f tok o _ => push3 z (Deliver f tok o)
        | TCancel f tok => push3 z (DeliverCancel f tok)
        end
      else y
  | Some (InNotify _ RSampleTerminal), WSample _ _ =>
      end3 (emit3 y (AViolation SampleTerminal)) VDefect
  | _, _ => y
  end.

Record Sys3 (R : Runtime) := { x3 : R3; r3 : rstate R }.
Arguments x3 {R} s.
Arguments r3 {R} s.

Definition step3 (R : Runtime) (I : Inputs) (Sch : Schedule) (s : Sys3 R) : Sys3 R :=
  let x := x3 s in
  let tick := fun y => mk3 (q3 y) (aw3 y) (l3 y) (cmd3 y) (cur3 y) (draws3 y) (tr3 y)
                         (done3 y) (S (micro3 x)) in
  if done3 x then s else
  match q3 x with
  | t :: rest =>
      let y := mk3 rest (aw3 x) (l3 x) (cmd3 x) (cur3 x) (draws3 x) (tr3 x) false (micro3 x) in
      let y := match task_action t with Some a => emit3 y a | None => y end in
      let '(y', r') := interp3 I y (run_task R (r3 s) t) in
      {| x3 := tick y'; r3 := r' |}
  | [] =>
      match aw3 x with
      | Some a => {| x3 := tick (entry3 I Sch x a); r3 := r3 s |}
      | None => {| x3 := tick x; r3 := r3 s |}
      end
  end.

Definition initial3 (R : Runtime) (p : prog R) (I : Inputs) : Sys3 R :=
  {| x3 := sample3 (mk3 [] None 0 0 0 0 [] false 0) TInitial; r3 := init R p (seed I) |}.

Fixpoint iterate3 (R : Runtime) (I : Inputs) (Sch : Schedule) (n : nat) (s : Sys3 R)
    : Sys3 R :=
  match n with O => s | S m => iterate3 R I Sch m (step3 R I Sch s) end.

Definition run3 (R : Runtime) (p : prog R) (I : Inputs) (Sch : Schedule) (n : nat)
    : list Action :=
  tr3 (x3 (iterate3 R I Sch n (initial3 R p I))).
