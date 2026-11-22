(** * S9 and S9_cancel are false in all three of their forms.

    First form (before 2026-11-22's amendments). Revision 3's executor ends the attempt with
    [AExit (VRoot r)] as soon as the root reports its exit. This executor closes instead,
    and its verdict is [VRoot r] only if no fiber is still live once closing has emptied the
    queue (X6.4). [outlive], a minimal runtime that meets the interface, keeps a child live
    beside the root; [masked_child] does the same on the concrete runtime.

    Second form (with [one_fiber], at 972c3e0). In [late_child] the child registers only
    during closing, after the root has left the live list, so at most one fiber is live at
    every step, and the verdicts differ as before.

    Current form (at most one registration). With a single fiber, a terminal sample failure
    is a violation in both executors, but this executor then closes: it interrupts the root,
    whose finalizer runs and reads the clock, and the read is recorded. Revision 3 ends the
    attempt at the violation. [clock_fin] refutes the current S9 and S9_cancel this way on
    the concrete runtime. Proofs of the rev3 domain. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Concrete Rev3 Statements Obligations Rev3Monitor.
From Durable Require Import Rev3ConcreteBase Rev3Concrete.
Import ListNotations.
Open Scope Z_scope.

(** ** A runtime in which a child outlives the root *)

(** The root registers, a child registers, the root exits and reports its exit; the child
    never exits. Every other task does nothing. *)
Definition outlive_task (s : bool) (t : Task) : Script bool :=
  match t with
  | StartRoot =>
      if s then Done s
      else Register 0%nat (fun _ => Register 1%nat (fun _ =>
             Emit (EvFiberExited 0%nat) (Emit (EvRootExit (ExitSuccess 0%nat)) (Done true))))
  | _ => Done s
  end.

Definition outlive : Runtime :=
  {| rstate := bool; prog := unit; requiv := eq; init := fun _ _ => false;
     run_task := outlive_task |}.

Definition outlive_inv (m : Mon) (s : bool) : Prop :=
  mpend m = [] /\
  (s = false -> ~ In 0%nat (mreg m) /\ ~ In 1%nat (mreg m) /\ ~ In 0%nat (mex m) /\
                ~ In 1%nat (mex m) /\ mrx m = false /\ mfirst m = None).

Lemma rev3_outlive_step : forall m s t, outlive_inv m s ->
  wp (mnext m (LTask t)) (run_task outlive s t) outlive_inv.
Proof.
  intros m s t [Hp Hf].
  assert (Hp' : mpend (mnext m (LTask t)) = []) by (simpl; rewrite Hp; reflexivity).
  assert (Hf' : s = false -> ~ In 0%nat (mreg (mnext m (LTask t))) /\
             ~ In 1%nat (mreg (mnext m (LTask t))) /\ ~ In 0%nat (mex (mnext m (LTask t))) /\
             ~ In 1%nat (mex (mnext m (LTask t))) /\ mrx (mnext m (LTask t)) = false /\
             mfirst (mnext m (LTask t)) = None).
  { intros E. destruct (Hf E) as [a [b [c [d [e f]]]]]. simpl. rewrite f.
    repeat split; assumption. }
  destruct t; simpl; try (split; [exact Hp'|exact Hf']).
  destruct s; [split; [exact Hp'|exact Hf']|].
  destruct (Hf eq_refl) as [H0 [H1 [He0 [He1 [Hrx Hfst]]]]].
  set (m1 := mnext m (LTask StartRoot)).
  assert (Hnp : forall f, no_pend m1 f) by (intros f tok; unfold m1; rewrite Hp'; simpl; tauto).
  intros b0. split.
  { apply rev3_mok_register; [exact H0|exact He0|apply Hnp]. }
  intros b1. split.
  { apply rev3_mok_register; [simpl; intros [H|H]; [discriminate|exact (H1 H)]|exact He1|].
    intros tok Hin. simpl in Hin. rewrite Hp in Hin. destruct Hin. }
  split.
  { apply (rev3_mok_fiber _ 0%nat); [reflexivity|exact I|simpl; right; left; reflexivity|
      exact He0|]. intros tok Hin. simpl in Hin. rewrite Hp in Hin. destruct Hin. }
  split.
  { apply (rev3_mok_root _ _ 0%nat); [exact Hrx|simpl; rewrite Hfst; reflexivity|
      simpl; left; reflexivity]. }
  split; [simpl; rewrite Hp; reflexivity|intro; discriminate].
Qed.

Theorem rev3_outlive_meets : Meets outlive.
Proof.
  split.
  - apply rev3_i1_of_eq. intros; simpl; tauto.
  - apply (rev3_meets_of_monitor outlive outlive_inv).
    + intros p seed. split; [reflexivity|]. intros _. simpl. tauto.
    + exact rev3_outlive_step.
Qed.

(** ** Helpers *)

Definition cx_inputs : Inputs :=
  {| entries := [InNotify 0%nat (RSample 5)]; persisted := []; foreign := fun _ => None;
     stream := fun _ => 0%nat; seed := 0%nat |}.

Definition cx_sched : Schedule := {| arrived := fun _ => 1%nat; cut_at := None; stop_at := None |}.

Lemma rev3_cx_valid : valid_schedule cx_inputs cx_sched.
Proof. split; intros; simpl; lia. Qed.

Definition cx_plain (m : Code) : Body := {| main := m; fin := CEnd 0 |}.

(** Whether a trace holds a sample command followed at once by a defect exit, the shape the
    second disjunct of S9_cancel looks for in revision 3's trace. *)
Fixpoint sample_then_defect (t : list Action) : bool :=
  match t with
  | [] => false
  | a :: rest =>
      match a, rest with
      | ACommand _ KSample None, AExit VDefect :: _ => true
      | _, _ => false
      end || sample_then_defect rest
  end.

Lemma rev3_sample_then_defect : forall pre c r,
  sample_then_defect ((pre ++ [ACommand c KSample None; AExit VDefect]) ++ r) = true.
Proof.
  induction pre as [|a pre IH]; intros c r; simpl; [reflexivity|].
  rewrite IH. apply orb_true_r.
Qed.

Ltac rev3_not_in := let H := fresh in intro H; simpl in H; intuition discriminate.

(** ** The first form *)

(** S9's conditions, S9 and S9_cancel as Statements.v stated them before 2026-11-22's
    amendments. *)
Definition s9_conditions_first_form (I : Inputs) (Sch : Schedule) (t : list Action) : Prop :=
  forallb (fun a => negb (other_fiber a)) t = true /\
  ~ In (AViolation Priority) t /\ ~ In (AViolation Blocked) t /\
  ~ In (AViolation Overflow) t /\ cut_at Sch = None /\ persisted I = [] /\
  (forall f tok d, In (AStart f tok (OSleep d)) t ->
     exists m, d = Millis m /\ m <= max_chunk) /\
  (forall k, foreign I k = None).

Definition S9_first_form : Prop :=
  forall R, Meets R -> forall p I Sch n1 n2,
    valid_schedule I Sch -> ~ In InCancel (entries I) ->
    s9_conditions_first_form I Sch (run R p I Sch n1) ->
    compatible (run R p I Sch n1) (run3 R p I Sch n2).

Definition S9_cancel_first_form : Prop :=
  forall R, Meets R -> forall p I Sch n1 n2,
    valid_schedule I Sch -> s9_conditions_first_form I Sch (run R p I Sch n1) ->
    compatible (run R p I Sch n1) (run3 R p I Sch n2) \/
    exists pre c, prefix (pre ++ [ACommand c KSample None; AExit VDefect]) (run3 R p I Sch n2)
                  /\ compatible (pre ++ [ACommand c KSample None; ACommand (S c) KSample None])
                                (run R p I Sch n1).

Lemma rev3_cx_run :
  run outlive tt cx_inputs cx_sched 10 =
  [ACommand 0 KSample None; ASampled 0 5 5 None; ARegister 0%nat; ARegister 1%nat; AExit VDefect].
Proof. vm_compute. reflexivity. Qed.

Lemma rev3_cx_run3 :
  run3 outlive tt cx_inputs cx_sched 10 =
  [ACommand 0 KSample None; ASampled 0 5 5 None; ARegister 0%nat; ARegister 1%nat;
   AExit (VRoot (ExitSuccess 0))].
Proof. vm_compute. reflexivity. Qed.

Lemma rev3_cx_conditions :
  s9_conditions_first_form cx_inputs cx_sched (run outlive tt cx_inputs cx_sched 10).
Proof.
  rewrite rev3_cx_run. unfold s9_conditions_first_form. simpl.
  repeat split; try reflexivity; try rev3_not_in.
  all: intros f tok d H; simpl in H; intuition discriminate.
Qed.

Lemma rev3_cx_incompatible :
  ~ compatible (run outlive tt cx_inputs cx_sched 10) (run3 outlive tt cx_inputs cx_sched 10).
Proof.
  rewrite rev3_cx_run, rev3_cx_run3.
  intros [[r Hr]|[r Hr]]; simpl in Hr; injection Hr; intros; congruence.
Qed.

Theorem rev3_not_s9_first_form : ~ S9_first_form.
Proof.
  intro H. apply rev3_cx_incompatible.
  apply (H outlive rev3_outlive_meets tt cx_inputs cx_sched 10%nat 10%nat rev3_cx_valid).
  - simpl. intros [H'|[]]. discriminate.
  - exact rev3_cx_conditions.
Qed.

Theorem rev3_not_s9_cancel_first_form : ~ S9_cancel_first_form.
Proof.
  intro H.
  destruct (H outlive rev3_outlive_meets tt cx_inputs cx_sched 10%nat 10%nat rev3_cx_valid
              rev3_cx_conditions) as [Hc|[pre [c [[r Hr] _]]]].
  - apply rev3_cx_incompatible. exact Hc.
  - clear H. pose proof (rev3_sample_then_defect pre c r) as E. rewrite <- Hr in E.
    rewrite rev3_cx_run3 in E. discriminate E.
Qed.

(** The root forks a child at once; the child masks itself and waits on a cell that is
    never written; the root returns 7. Closing interrupts the child, which only records the
    request, so the child stays live. *)
Definition masked_child : CProg :=
  {| bodies := fun i => match i with
       | O => cx_plain (CFork true 1 (fun _ => CEnd 7))
       | _ => cx_plain (CMaskOn (CAwaitCell 5 (fun _ => CEnd 0)))
       end;
     root_body := 0 |}.

Theorem rev3_masked_child_diverges :
  run concrete masked_child cx_inputs cx_sched 20 =
    [ACommand 0 KSample None; ASampled 0 5 5 None; ARegister 0%nat; ARegister 1%nat; AExit VDefect] /\
  run3 concrete masked_child cx_inputs cx_sched 20 =
    [ACommand 0 KSample None; ASampled 0 5 5 None; ARegister 0%nat; ARegister 1%nat;
     AExit (VRoot (ExitSuccess 7))].
Proof. split; vm_compute; reflexivity. Qed.

(** With [MeetsConcrete], the masked child refutes the first form of S9 on the concrete
    runtime itself. *)
Theorem rev3_not_s9_first_form_concrete : ~ S9_first_form.
Proof.
  intro H. destruct rev3_masked_child_diverges as [E1 E2].
  assert (Hcond : s9_conditions_first_form cx_inputs cx_sched
                    (run concrete masked_child cx_inputs cx_sched 20%nat)).
  { rewrite E1. unfold s9_conditions_first_form. simpl.
    repeat split; try reflexivity; try rev3_not_in.
    all: intros f tok d H'; simpl in H'; intuition discriminate. }
  pose proof (H concrete rev3_meets_concrete masked_child cx_inputs cx_sched 20%nat 20%nat
    rev3_cx_valid ltac:(simpl; intros [H'|[]]; discriminate) Hcond) as Hc.
  clear H. rewrite E1, E2 in Hc.
  destruct Hc as [[r Hr]|[r Hr]]; simpl in Hr; injection Hr; intros; congruence.
Qed.

(** The root queues a child and awaits a run; the child interrupts the root, whose await is
    released; the root's finalizer starts a second run. This executor holds the second run
    until the released command settles (X5); revision 3 ignores the release and records a
    second operation. *)
Definition released_root : CProg :=
  {| bodies := fun i => match i with
       | O => {| main := CFork false 1 (fun _ => CStart (ORun 1 0) (fun _ => CEnd 0));
                 fin := CStart (ORun 2 0) (fun _ => CEnd 0) |}
       | _ => cx_plain (CInterrupt 0%nat (CEnd 0))
       end;
     root_body := 0 |}.

Definition released_inputs : Inputs :=
  {| entries := [InNotify 0%nat (RSample 5); InNotify 1%nat (ROutcome (Value 0));
                 InNotify 2%nat (ROutcome (Value 0)); InNotify 3%nat (RSample 6)];
     persisted := []; foreign := fun _ => None; stream := fun _ => 0%nat; seed := 0%nat |}.

Definition released_sched : Schedule :=
  {| arrived := fun _ => 4%nat; cut_at := None; stop_at := None |}.

Theorem rev3_released_root_diverges :
  run concrete released_root released_inputs released_sched 30 =
    [ACommand 0 KSample None; ASampled 0 5 5 None; ARegister 0%nat; AStart 0%nat 0%nat (ORun 1 0);
     ACommand 1 (KOp (ORun 1 0)) (Some (0, 0)%nat); ARegister 1%nat;
     AStart 0%nat 1%nat (ORun 2 0); ACommand 2 (KOp (ORun 2 0)) (Some (0, 1)%nat);
     ACommand 3 KSample None; ASampled 3 6 6 None; ADelivered 0%nat 1%nat (Value 0);
     AExit (VRoot ExitInterrupted)] /\
  run3 concrete released_root released_inputs released_sched 30 =
    [ACommand 0 KSample None; ASampled 0 5 5 None; ARegister 0%nat; AStart 0%nat 0%nat (ORun 1 0);
     ACommand 1 (KOp (ORun 1 0)) (Some (0, 0)%nat); ARegister 1%nat;
     AStart 0%nat 1%nat (ORun 2 0); AViolation SecondOp; AExit VDefect].
Proof. split; vm_compute; reflexivity. Qed.

(** ** The second form *)

(** S9's conditions, [one_fiber], S9 and S9_cancel as Statements.v stated them at 972c3e0. *)
Definition s9_conditions_second_form (I : Inputs) (Sch : Schedule) (t : list Action)
    : Prop :=
  forallb (fun a => negb (other_fiber a)) t = true /\
  ~ In (AViolation Priority) t /\ ~ In (AViolation Blocked) t /\
  ~ In (AViolation Overflow) t /\ cut_at Sch = None /\ persisted I = [] /\
  (forall f tok d, In (AStart f tok (OSleep d)) t ->
     exists m, d = Millis m /\ m <= max_chunk) /\
  (forall k, foreign I k = None).

Definition one_fiber_second_form (R : Runtime) (p : prog R) (I : Inputs) (Sch : Schedule)
    (n : nat) : Prop :=
  forall k, (k <= n)%nat -> (length (live (xs (iterate R I Sch k (initial R p I)))) <= 1)%nat.

Definition S9_second_form : Prop :=
  forall R, Meets R -> forall p I Sch n1 n2,
    valid_schedule I Sch -> ~ In InCancel (entries I) -> one_fiber_second_form R p I Sch n1 ->
    s9_conditions_second_form I Sch (run R p I Sch n1) ->
    compatible (run R p I Sch n1) (run3 R p I Sch n2).

Definition S9_cancel_second_form : Prop :=
  forall R, Meets R -> forall p I Sch n1 n2,
    valid_schedule I Sch -> one_fiber_second_form R p I Sch n1 ->
    s9_conditions_second_form I Sch (run R p I Sch n1) ->
    compatible (run R p I Sch n1) (run3 R p I Sch n2) \/
    exists pre c, prefix (pre ++ [ACommand c KSample None; AExit VDefect]) (run3 R p I Sch n2)
                  /\ compatible (pre ++ [ACommand c KSample None; ACommand (S c) KSample None])
                                (run R p I Sch n1).

(** The root returns 7; its finalizer queues a child. The child runs only during closing,
    is interrupted at registration, and its finalizer masks itself and waits on a cell that
    is never written. *)
Definition late_child : CProg :=
  {| bodies := fun i => match i with
       | O => {| main := CEnd 7; fin := CFork false 1 (fun _ => CEnd 0) |}
       | _ => {| main := CEnd 0; fin := CMaskOn (CAwaitCell 5 (fun _ => CEnd 0)) |}
       end;
     root_body := 0 |}.

Lemma rev3_late_child_runs :
  run concrete late_child cx_inputs cx_sched 20 =
    [ACommand 0 KSample None; ASampled 0 5 5 None; ARegister 0%nat; ARegister 1%nat; AExit VDefect] /\
  run3 concrete late_child cx_inputs cx_sched 20 =
    [ACommand 0 KSample None; ASampled 0 5 5 None; ARegister 0%nat; AExit (VRoot (ExitSuccess 7))].
Proof. split; vm_compute; reflexivity. Qed.

Definition late_live_ok (k : nat) : bool :=
  (length (live (xs (iterate concrete cx_inputs cx_sched k
                       (initial concrete late_child cx_inputs)))) <=? 1)%nat.

Lemma rev3_late_child_live : forallb late_live_ok (seq 0 21) = true.
Proof. vm_compute. reflexivity. Qed.

(** At most one fiber is live at every step: the root leaves the live list before the child
    joins it. *)
Lemma rev3_late_child_one_fiber :
  one_fiber_second_form concrete late_child cx_inputs cx_sched 20%nat.
Proof.
  intros k Hk. pose proof rev3_late_child_live as H.
  rewrite forallb_forall in H. specialize (H k ltac:(apply in_seq; lia)).
  unfold late_live_ok in H. apply Nat.leb_le in H. exact H.
Qed.

Lemma rev3_late_child_conditions :
  s9_conditions_second_form cx_inputs cx_sched (run concrete late_child cx_inputs cx_sched 20%nat).
Proof.
  rewrite (proj1 rev3_late_child_runs). unfold s9_conditions_second_form. simpl.
  repeat split; try reflexivity; try rev3_not_in.
  all: intros f tok d H; simpl in H; intuition discriminate.
Qed.

Lemma rev3_late_child_incompatible :
  ~ compatible (run concrete late_child cx_inputs cx_sched 20%nat)
               (run3 concrete late_child cx_inputs cx_sched 20%nat).
Proof.
  destruct rev3_late_child_runs as [E1 E2]. rewrite E1, E2.
  intros [[r Hr]|[r Hr]]; simpl in Hr; injection Hr; intros; congruence.
Qed.

Theorem rev3_not_s9_second_form : ~ S9_second_form.
Proof.
  intro H. apply rev3_late_child_incompatible.
  apply (H concrete rev3_meets_concrete late_child cx_inputs cx_sched 20%nat 20%nat
           rev3_cx_valid).
  - simpl. intros [H'|[]]. discriminate.
  - exact rev3_late_child_one_fiber.
  - exact rev3_late_child_conditions.
Qed.

Theorem rev3_not_s9_cancel_second_form : ~ S9_cancel_second_form.
Proof.
  intro H.
  destruct (H concrete rev3_meets_concrete late_child cx_inputs cx_sched 20%nat 20%nat
              rev3_cx_valid rev3_late_child_one_fiber rev3_late_child_conditions)
    as [Hc|[pre [c [[r Hr] _]]]].
  - apply rev3_late_child_incompatible. exact Hc.
  - clear H. pose proof (rev3_sample_then_defect pre c r) as E. rewrite <- Hr in E.
    rewrite (proj2 rev3_late_child_runs) in E. discriminate E.
Qed.

(** ** The current form *)

(** One fiber. The root awaits a run whose result's sample fails terminally. Both executors
    record the violation; this executor then closes and interrupts the root, whose
    finalizer reads the clock before the attempt ends. Revision 3 ends at the violation. *)
Definition clock_fin : CProg :=
  {| bodies := fun _ => {| main := CStart (ORun 1 0) (fun _ => CEnd 0);
                           fin := CClock (fun _ => CEnd 0) |};
     root_body := 0 |}.

Definition terminal_inputs : Inputs :=
  {| entries := [InNotify 0%nat (RSample 5); InNotify 1%nat (ROutcome (Value 0));
                 InNotify 2%nat RSampleTerminal];
     persisted := []; foreign := fun _ => None; stream := fun _ => 0%nat; seed := 0%nat |}.

Definition terminal_sched : Schedule :=
  {| arrived := fun _ => 3%nat; cut_at := None; stop_at := None |}.

Lemma rev3_terminal_valid : valid_schedule terminal_inputs terminal_sched.
Proof. split; intros; simpl; lia. Qed.

Lemma rev3_clock_fin_runs :
  run concrete clock_fin terminal_inputs terminal_sched 20 =
    [ACommand 0 KSample None; ASampled 0 5 5 None; ARegister 0%nat; AStart 0%nat 0%nat (ORun 1 0);
     ACommand 1 (KOp (ORun 1 0)) (Some (0, 0)%nat); ACommand 2 KSample None;
     AViolation SampleTerminal; AClock 0%nat 5; AExit VDefect] /\
  run3 concrete clock_fin terminal_inputs terminal_sched 20 =
    [ACommand 0 KSample None; ASampled 0 5 5 None; ARegister 0%nat; AStart 0%nat 0%nat (ORun 1 0);
     ACommand 1 (KOp (ORun 1 0)) (Some (0, 0)%nat); ACommand 2 KSample None;
     AViolation SampleTerminal; AExit VDefect].
Proof. split; vm_compute; reflexivity. Qed.

Lemma rev3_clock_fin_conditions :
  s9_conditions terminal_inputs terminal_sched
    (run concrete clock_fin terminal_inputs terminal_sched 20%nat).
Proof.
  rewrite (proj1 rev3_clock_fin_runs). unfold s9_conditions, registrations. simpl.
  repeat split; try reflexivity; try rev3_not_in.
  all: intros f tok d H; simpl in H; intuition discriminate.
Qed.

Lemma rev3_clock_fin_incompatible :
  ~ compatible (run concrete clock_fin terminal_inputs terminal_sched 20%nat)
               (run3 concrete clock_fin terminal_inputs terminal_sched 20%nat).
Proof.
  destruct rev3_clock_fin_runs as [E1 E2]. rewrite E1, E2.
  intros [[r Hr]|[r Hr]]; simpl in Hr; injection Hr; intros; congruence.
Qed.

Theorem rev3_not_s9 : ~ S9.
Proof.
  intro H. apply rev3_clock_fin_incompatible.
  apply (H concrete rev3_meets_concrete clock_fin terminal_inputs terminal_sched 20%nat 20%nat
           rev3_terminal_valid).
  - simpl. intuition discriminate.
  - exact rev3_clock_fin_conditions.
Qed.

Theorem rev3_not_s9_cancel : ~ S9_cancel.
Proof.
  intro H.
  destruct (H concrete rev3_meets_concrete clock_fin terminal_inputs terminal_sched 20%nat 20%nat
              rev3_terminal_valid rev3_clock_fin_conditions) as [Hc|[pre [c [[r Hr] _]]]].
  - apply rev3_clock_fin_incompatible. exact Hc.
  - clear H. pose proof (rev3_sample_then_defect pre c r) as E. rewrite <- Hr in E.
    rewrite (proj2 rev3_clock_fin_runs) in E. discriminate E.
Qed.

(** ** A second divergence of the current form, with no violation *)

(** A runtime with one fiber whose await is released without an interruption request. The
    root queues task 7 and awaits a run; task 7 reports the root's release and a second
    run. The interface allows a release report at any time (I4). This executor holds the
    second run until the released command settles; revision 3 ignores the release and
    records a second operation. Excluding violations from S9's conditions would not exclude
    this run, since this executor records none. *)
Definition release_task (s : nat) (t : Task) : Script nat :=
  match s, t with
  | O, StartRoot =>
      Register 0%nat (fun _ => Emit (EvQueue 0%nat 7%nat) (Emit (EvStart 0%nat 0%nat (ORun 1 0)) (Done 1%nat)))
  | S O, RunQueued t =>
      if Nat.eqb t 7%nat then Emit (EvRelease 0%nat 0%nat) (Emit (EvStart 0%nat 1%nat (ORun 2 0)) (Done 2%nat))
      else Done s
  | _, _ => Done s
  end.

Definition spontaneous : Runtime :=
  {| rstate := nat; prog := unit; requiv := eq; init := fun _ _ => 0%nat;
     run_task := release_task |}.

Definition spontaneous_inv (m : Mon) (s : nat) : Prop :=
  (s = 0%nat -> ~ In 0%nat (mreg m) /\ ~ In 0%nat (mex m) /\ no_pend m 0%nat /\
                ~ In 0%nat (mtoks m) /\ ~ In 1%nat (mtoks m)) /\
  (s = 1%nat -> In 0%nat (mreg m) /\ ~ In 0%nat (mex m) /\
                (forall t, In (0%nat, t) (mpend m) -> t = 0%nat) /\ ~ In 1%nat (mtoks m)).

Lemma rev3_spontaneous_step : forall m s t, spontaneous_inv m s ->
  wp (mnext m (LTask t)) (run_task spontaneous s t) spontaneous_inv.
Proof.
  intros m s t [H0 H1].
  set (m1 := mnext m (LTask t)).
  assert (Hp : forall g tok, In (g, tok) (mpend m1) -> In (g, tok) (mpend m))
    by (intros g tok Hin; exact (proj1 (rev3_pend_task _ _ _ _ Hin))).
  assert (Hi : spontaneous_inv m1 s).
  { split.
    - intros E. destruct (H0 E) as [a [b [c [d e]]]]. repeat split; try assumption.
      intros tok Hin. exact (c tok (Hp _ _ Hin)).
    - intros E. destruct (H1 E) as [a [b [c d]]]. repeat split; try assumption.
      intros tok Hin. exact (c tok (Hp _ _ Hin)). }
  destruct s as [|[|s]]; simpl; [destruct t|destruct t|exact Hi]; try exact Hi.
  - destruct (H0 eq_refl) as [Hr [He [Hn [Ht0 Ht1]]]]. intros b.
    split; [apply rev3_mok_register; [exact Hr|exact He|intros tok Hin; exact (Hn tok (Hp _ _ Hin))]|].
    split; [apply rev3_mok_queue|].
    rewrite (Rev3ConcreteBase.rev3_mnext_quiet _ (LEvent (EvQueue 0%nat 7%nat))) by exact I.
    split.
    + apply rev3_mok_start; simpl.
      * left. reflexivity.
      * exact He.
      * intros tok Hin. simpl in Hin. apply filter_In in Hin. exact (Hn tok (Hp _ _ (proj1 Hin))).
      * exact Ht0.
    + split; intros E; [discriminate|]. simpl. split; [left; reflexivity|split; [exact He|split]].
      * intros t' [E'|Hin]; [injection E' as <-; reflexivity|].
        apply filter_In in Hin. destruct Hin as [Hin _]. apply filter_In in Hin.
        destruct Hin as [Hin _]. destruct (Hn t' (Hp _ _ Hin)).
      * intros [E'|Hin]; [discriminate|exact (Ht1 Hin)].
  - destruct (H1 eq_refl) as [Hr [He [Hpd Ht1]]].
    match goal with |- context [Nat.eqb ?q 7%nat] => destruct (Nat.eqb q 7%nat) end;
      [|exact Hi].
    split.
    + apply rev3_mok_release; [exact Hr|exact He|]. intros t' Hin. exact (Hpd t' (Hp _ _ Hin)).
    + split.
      * apply rev3_mok_start; simpl.
        -- exact Hr.
        -- exact He.
        -- intros tok Hin. apply rev3_pend_release in Hin. destruct Hin as [Hin Hne].
           apply Hne. split; [reflexivity|exact (Hpd tok (Hp _ _ Hin))].
        -- exact Ht1.
      * split; intros E; discriminate.
Qed.

Theorem rev3_spontaneous_meets : Meets spontaneous.
Proof.
  split.
  - apply rev3_i1_of_eq. intros; simpl; tauto.
  - apply (rev3_meets_of_monitor spontaneous spontaneous_inv).
    + intros p seed. split; intros E; [|discriminate]. unfold no_pend. simpl.
      repeat split; intros; tauto.
    + exact rev3_spontaneous_step.
Qed.

Definition spontaneous_inputs : Inputs :=
  {| entries := [InNotify 0%nat (RSample 5); InNotify 1%nat (ROutcome (Value 0))];
     persisted := []; foreign := fun _ => None; stream := fun _ => 0%nat; seed := 0%nat |}.

Definition spontaneous_sched : Schedule :=
  {| arrived := fun _ => 2%nat; cut_at := None; stop_at := None |}.

Theorem rev3_spontaneous_diverges :
  run spontaneous tt spontaneous_inputs spontaneous_sched 20 =
    [ACommand 0 KSample None; ASampled 0 5 5 None; ARegister 0%nat;
     AStart 0%nat 0%nat (ORun 1 0); ACommand 1 (KOp (ORun 1 0)) (Some (0, 0)%nat);
     AStart 0%nat 1%nat (ORun 2 0); ACommand 2 (KOp (ORun 2 0)) (Some (0, 1)%nat)] /\
  run3 spontaneous tt spontaneous_inputs spontaneous_sched 20 =
    [ACommand 0 KSample None; ASampled 0 5 5 None; ARegister 0%nat;
     AStart 0%nat 0%nat (ORun 1 0); ACommand 1 (KOp (ORun 1 0)) (Some (0, 0)%nat);
     AStart 0%nat 1%nat (ORun 2 0); AViolation SecondOp; AExit VDefect].
Proof. split; vm_compute; reflexivity. Qed.

(** The same refutation of S9 with no violation in this executor's trace. *)
Theorem rev3_not_s9_without_violation : ~ S9.
Proof.
  intro H. destruct rev3_spontaneous_diverges as [E1 E2].
  assert (Hc : s9_conditions spontaneous_inputs spontaneous_sched
                 (run spontaneous tt spontaneous_inputs spontaneous_sched 20%nat)).
  { rewrite E1. unfold s9_conditions, registrations. simpl.
    repeat split; try reflexivity; try rev3_not_in.
    all: intros f tok d H'; simpl in H'; intuition discriminate. }
  pose proof (H spontaneous rev3_spontaneous_meets tt spontaneous_inputs spontaneous_sched
    20%nat 20%nat ltac:(split; intros; simpl; lia) ltac:(simpl; intuition discriminate) Hc)
    as Hk.
  clear H. rewrite E1, E2 in Hk.
  destruct Hk as [[r Hr]|[r Hr]]; simpl in Hr; injection Hr; intros; congruence.
Qed.
