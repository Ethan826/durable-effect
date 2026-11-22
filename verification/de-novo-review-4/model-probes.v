From Coq Require Import List ZArith Arith.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model Executor Statements.
Import ListNotations.
Close Scope Z_scope.
Definition ev {T} (e : FiberE T) (k : T -> itree FiberE unit) := Vis e k.
Definition stop : itree FiberE unit := Ret tt.
Definition clock := ev ReadClock (fun _ => stop).
Definition draw := ev Draw (fun _ => stop).
Definition call (arg : nat) (k : Outcome -> itree FiberE unit) := ev (StartAwait 4 arg) k.
Definition sleep d t := ev (Sleep d) (fun _ => t).
Definition body t f := {| main := t; finalizer := f |}.
Definition one t f := {| root := 0; bodies := fun _ => body t f |}.
Definition two t f c cf := {| root := 0; bodies := fun n => if Nat.eqb n 0 then body t f else body c cf |}.
Definition environment (t : nat -> Z) (o : Outcome) (c : nat -> bool) (e : option (nat * Ending)) :=
  {| outcome_of := fun _ => o; sample_of := fun i => {| true_time := t i; host_error := 0%Z |};
     cancelled_at := c; random_of := fun _ => 7%nat; ends_at := e |}.
Definition base := environment (fun _ => 100%Z) (Value 9) (fun _ => false) None.
Definition ending n how := environment (fun _ => 100%Z) (Value 9) (fun _ => false) (Some (n, how)).
Definition cancelled := environment (fun _ => 100%Z) (Value 9) (Nat.eqb 0) None.
Definition failed := environment (fun _ => 100%Z) (Failure 9) (fun _ => false) None.
Definition now : Arrival := fun _ _ => true.
Definition late : Arrival := fun _ i => Nat.leb 5 i.
Definition never : Arrival := fun _ _ => false.
Definition pulse : Arrival := fun _ i => Nat.eqb 5 i.
Definition st P E A X n := iterate policy_v1 P E A X n (initial P E).
Definition waiting := one (call 11 (fun _ => clock)) stop.
Definition empty_wait := one (ev WaitOutside (fun _ => clock)) stop.
Definition runner := two (ev (Fork Queued 1) (fun h => call 11 (fun _ => ev (ReadRef 0)
  (fun n => call n (fun _ => clock))))) stop (ev (WriteRef 0 42) (fun _ => stop)) stop.
Definition two_calls := two (ev (Fork Queued 1) (fun _ => call 11 (fun _ => stop)))
  clock (call 12 (fun _ => stop)) stop.
Definition outside (P h : nat) := fun i => if Nat.eqb P i then Some (h, 9%nat) else None.
Definition outside_child := two (ev (Fork Immediate 1) (fun _ => call 11 (fun _ => stop)))
  clock (ev WaitOutside (fun _ => draw)) stop.
Definition interrupted := two (ev (Fork Immediate 1)
  (fun h => ev (Interrupt h) (fun _ => ev (ReadRef 0)
    (fun n => call n (fun _ => stop))))) stop
  (call 12 (fun _ => stop)) (ev (WriteRef 0 1) (fun _ => clock)).
Definition abandoned_wait := two (ev (Fork Immediate 1)
  (fun h => ev (Interrupt h) (fun _ => call 11 (fun _ => clock)))) stop
  (call 12 (fun _ => stop)) stop.
Definition abandon_changed :=
  {| outcome_of := fun n => if Nat.eqb n 0 then Failure 2 else Value 9;
     sample_of := sample_of base; cancelled_at := Nat.eqb 0;
     random_of := random_of base; ends_at := None |}.
Definition abandon_arrives : Arrival := fun op i => if Nat.eqb op 0 then Nat.leb 3 i else true.
Definition detached := two (ev (Fork Queued 1) (fun _ => stop)) stop
  (call 12 (fun _ => stop)) clock.
Definition all_done := two (ev (Fork Queued 1) (fun _ => stop)) clock stop draw.
Definition chain := one (sleep (Millis (max_chunk + 1)%Z) clock) stop.
Definition infinity := one (sleep Forever clock) stop.
Definition lead_case := one (sleep (Millis 1%Z) (sleep (Millis 1%Z) clock)) stop.
Definition falling := environment (fun i => if Nat.eqb i 0 then 100%Z else 90%Z) (Value 9) (fun _ => false) None.
Definition draw_pair :=
  two (ev (Fork Queued 1) (fun _ => call 11 (fun _ => draw))) stop draw stop.
Fixpoint taus n (t : itree FiberE unit) := match n with O => t | S m => Tau (taus m t) end.
Definition fuel_edge :=
  two (taus 2047 (ev (Fork Immediate 1) (fun _ => draw))) stop clock stop.
Definition point_s2 := run waiting base now 4.
Definition no_effect n := run waiting base now n.
Definition no_clock := one (call 11 (fun _ => stop)) stop.
Definition negative_end := one (sleep (Millis 0%Z) clock) clock.

(* S1 and S1_end: same quiescence, different finite prefixes, cut a nonempty turn. *)
Eval vm_compute in (run runner base now 12, run runner base late 12, run runner base late 3,
                    run runner base pulse 12).
Eval vm_compute in (run runner (ending 1 EndSuspend) now 5,
  queue (st runner base now no_outside_resumes 1), run runner (ending 1 EndCrash) now 5).
(* S2: count-based cut keeps the next sample command and the sample before missing delivery. *)
Eval vm_compute in (point_s2, cut 0 2 point_s2, cut 0 0 point_s2,
  run waiting (ending 1 EndCrash) now 4, run waiting base now 4).
(* S3/S4: actual guard, delay-limited prefix, synthetic trace distinction. *)
Eval vm_compute in (run two_calls base now 5, run two_calls base late 1,
  run two_calls base late 5,
  ends_wait 0 0 (SleepCommand 1 0 1%Z),
  run waiting cancelled now 6).
Goal single_await [Command 0 0 4 11; Command 1 0 4 12].
Proof.
  cbn. split.
  - intros pre b post H _ op h Hb. destruct pre as [|x pre]; inversion H; subst;
    [inversion Hb; reflexivity | destruct pre; discriminate].
  - split; [intros pre b post H; destruct pre; discriminate | exact I].
Qed.
(* S5/S6: a valid detected resume, spurious priority, ordinary blocked and awaited cases. *)
Eval vm_compute in (run_with outside_child base never (outside 1 1) 4,
  run_with outside_child (ending 1 EndCrash) never (outside 1 1) 4,
  run_with waiting base now (fun _ => Some (2%nat, 0%nat)) 5,
  run empty_wait base now 5, run waiting base never 5).
(* S7: delivery has no sample-pending state; end wins; intermediate links leave queue empty. *)
Eval vm_compute in (run waiting base now 1, run waiting base now 2,
  run waiting (ending 2 EndCrash) now 6,
  run chain base now 2, queue (st chain base now no_outside_resumes 2), run chain base now 5).
(* S8: clamp, cancellation, chunking, infinite prefix, lead. *)
Eval vm_compute in (run waiting falling now 5, run waiting failed now 5, run chain cancelled now 6,
  run infinity base now 5, run lead_case base now 6, run negative_end base now 5).
(* S9: common normal path, different admissibility domains, revision-only differences. *)
Eval vm_compute in (run waiting base now 5, run_rev3 waiting base now 5,
  run empty_wait base now 1, run_rev3 empty_wait base now 1,
  run empty_wait base now 5, run_rev3 empty_wait base now 5,
  run_rev3 chain base now 5, run_rev3 infinity base now 5, run_rev3 waiting cancelled now 5).
(* S10: equality of values is blind to fiber ownership. *)
Eval vm_compute in (run draw_pair base now 8, run draw_pair base late 12,
  draws_of [Drawn 0 7; Drawn 1 8], draws_of [Drawn 1 7; Drawn 0 8]).
(* S11: ignored outcome, cancel, and timing for abandoned op. *)
Eval vm_compute in (abandoned (st abandoned_wait base now no_outside_resumes 1),
  run abandoned_wait base now 8, run abandoned_wait abandon_changed now 8,
  run abandoned_wait abandon_changed abandon_arrives 8).
(* Lifetime, finalizer synchrony, immediate nested evaluation. *)
Eval vm_compute in (run detached base never 6, root_done (st detached base never no_outside_resumes 6),
  run all_done base now 6, run interrupted base now 6, run fuel_edge base now 5).

Definition fuel_overtake :=
  {| root := 0; bodies := fun n =>
    if Nat.eqb n 0 then body (taus 2046 (ev (Fork Queued 1)
      (fun _ => ev (Fork Immediate 2) (fun _ => stop)))) stop
    else if Nat.eqb n 1 then body draw stop else body clock stop |}.
Definition with_finalizer := one (call 11 (fun _ => stop)) clock.
Definition initial_high := environment (fun _ => 9007199254740992%Z)
  (Value 9) (fun _ => false) None.
Definition cancelled_upper_gap :=
  let pre := st chain cancelled now no_outside_resumes 1 in
  let post := st chain cancelled now no_outside_resumes 2 in
  (awaited pre, Z.geb (true_time (sample_of cancelled 1))
     (true_time (sample_of cancelled 0) + max_chunk), logical post).
Eval vm_compute in (run fuel_overtake base now 1, run fuel_overtake base now 5,
  run with_finalizer base now 5, run with_finalizer (ending 1 EndSuspend) now 5).
Eval vm_compute in (run (one (sleep (Millis 1%Z) clock) stop) initial_high now 5,
  cancelled_upper_gap).

(* P7 distinguishes the unmodelled host reading at completion from the recorded sample. *)
Eval vm_compute in
  (logical (st waiting falling now no_outside_resumes 2), 110%Z,
   Z.geb (logical (st waiting falling now no_outside_resumes 2)) 110%Z).
(* S2 cannot return agreement on an externally provided command journal. *)
Eval vm_compute in (cut 0 1 point_s2, command_of (Command 0 0 4 99)).
(* Checked S9 premise witnesses for a single call. *)
Goal single_fiber waiting.
Proof.
  split.
  - eapply nf_vis with (e := StartAwait 4 11) (k := fun _ => clock).
    + reflexivity.
    + exact I.
    + intro outcome. eapply nf_vis with (e := ReadClock) (k := fun _ => stop).
      * reflexivity.
      * exact I.
      * intro millis. eapply nf_ret. reflexivity.
  - eapply nf_ret. reflexivity.
Qed.

Definition busy_outside := two (ev (Fork Immediate 1) (fun _ => ev YieldNow (fun _ => clock)))
  stop (ev WaitOutside (fun _ => draw)) stop.
Definition branch_fork := one (call 11
  (fun o => match o with Value _ => clock | Failure _ => ev (Fork Queued 1) (fun _ => stop) end))
  stop.
Eval vm_compute in (queue (st busy_outside base now no_outside_resumes 1),
  run_with busy_outside base now (outside 1 1) 5, run busy_outside base now 5,
  run branch_fork base now 5, run_rev3 branch_fork base now 5).

Definition late_violation := two (call 13 (fun _ =>
  ev (Fork Queued 1) (fun _ => call 11 (fun _ => stop))))
  stop (call 12 (fun _ => stop)) stop.
Eval vm_compute in (run late_violation base now 8, run late_violation base never 8).
Eval vm_compute in (run waiting (ending 1 EndCrash) late 5,
  run waiting (ending 2 EndSuspend) now 5).
