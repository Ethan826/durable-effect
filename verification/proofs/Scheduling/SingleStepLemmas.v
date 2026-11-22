(** * Lemmas for the single-step statements S4 to S8.

    A generic preservation argument: a property of the trace, the awaited operation, the next
    operation index and [L] that is closed under each kind of change the executor makes holds
    after [run_fiber], [interrupt_fiber], a whole micro-step, and every reachable state. *)

From Coq Require Import List ZArith Bool Arith Lia.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model Executor Statements.
Import ListNotations.
Open Scope Z_scope.

(** ** Properties of the four tracked fields *)

Definition Inv := list Action -> option Awaited -> nat -> Z -> Prop.

Definition holds (Q : Inv) (st : State) : Prop :=
  Q (trace st) (awaited st) (next_op st) (logical st).

(** An action that is not a command and not the outside-resume violation. *)
Definition quiet (a : Action) : Prop :=
  command_of a = None /\ a <> Violated StepOutsideTurn.

Definition awaited_handle (aw : Awaited) : nat :=
  match aw with AwaitOp h _ | AwaitSleep h _ _ _ => h end.

(** The awaited operation after fiber [h] is interrupted. *)
Definition cleared (aw : option Awaited) (h : nat) : option Awaited :=
  match aw with
  | Some a => if Nat.eqb (awaited_handle a) h then None else Some a
  | None => None
  end.

(** A sleep's chunk and the rest of its chain are in range. *)
Definition chain_ok (c : Z) (r : Chain) : Prop :=
  0 < c <= max_chunk /\ (forall d, r = Remaining d -> 0 < d).

(** What a policy guarantees of the chain it starts for a sleep. *)
Definition start_ok (pol : Policy) (c : Z) (r : Chain) : Prop :=
  if chunk_long_sleeps pol then chain_ok c r else True.

(** The next link of a sleep chain, as [deliver] computes it. *)
Definition next_link (r : Chain) : option (Z * Chain) :=
  match r with
  | NoChain => None
  | Remaining d =>
      Some (if d <=? max_chunk then (d, NoChain) else (max_chunk, Remaining (d - max_chunk)))
  | Endless => Some (max_chunk, Endless)
  end.

(** The floor a delivery may add to [L]: none, or the awaited sleep's chunk. *)
Definition floor_ok (aw : Awaited) (floor : Z) : Prop :=
  floor = 0 \/ exists h op r, aw = AwaitSleep h op floor r.

(** Closure under the changes [run_fiber] and [interrupt_fiber] make. *)
Record closed (pol : Policy) (Q : Inv) : Prop := {
  c_quiet : forall tr aw n l a, quiet a -> Q tr aw n l -> Q (tr ++ [a]) aw n l;
  c_interrupt : forall tr aw n l h,
    Q tr aw n l -> Q (tr ++ [Interrupted h]) (cleared aw h) n l;
  c_command : forall tr n l h k a,
    Q tr None n l -> Q (tr ++ [Command n h k a]) (Some (AwaitOp h n)) (S n) l;
  c_sleep : forall tr n l h c r, start_ok pol c r ->
    Q tr None n l -> Q (tr ++ [SleepCommand n h c]) (Some (AwaitSleep h n c r)) (S n) l
}.

(** Closure under the further changes a delivery makes. *)
Record closed_turn (Q : Inv) : Prop := {
  c_sample : forall tr aw n l i s floor, floor_ok aw floor -> Q tr (Some aw) n l ->
    Q ((tr ++ [SampleCommand i]) ++ [Sampled i s]) (Some aw) n (next_logical l floor s);
  c_deliver : forall tr aw n l o, Q tr (Some aw) n l ->
    Q (tr ++ [Delivered (awaited_op aw) (awaited_handle aw) o]) None n l;
  c_link : forall tr h op c r n l c' r', next_link r = Some (c', r') ->
    Q tr (Some (AwaitSleep h op c r)) n l ->
    Q (tr ++ [SleepCommand n h c']) (Some (AwaitSleep h n c' r')) (S n) l
}.

Section Generic.

Variable pol : Policy.
Variable Q : Inv.
Hypothesis HQ : closed pol Q.

Lemma emit_holds : forall st a, quiet a -> holds Q st -> holds Q (emit st a).
Proof. intros st a Ha H. apply (c_quiet _ _ HQ); assumption. Qed.

Lemma quiet_exit : forall e, quiet (Exited e).
Proof. intros e. split; [reflexivity | discriminate]. Qed.

Lemma quiet_violation : forall v, v <> StepOutsideTurn -> quiet (Violated v).
Proof. intros v Hv. split; [reflexivity | congruence]. Qed.

Lemma finish_holds : forall st e, holds Q st -> holds Q (finish st e).
Proof. intros st e H. apply emit_holds; [apply quiet_exit | exact H]. Qed.

Lemma violate_holds : forall st v,
  v <> StepOutsideTurn -> holds Q st -> holds Q (violate st v).
Proof.
  intros st v Hv H. apply finish_holds. apply emit_holds; [|exact H].
  apply quiet_violation; exact Hv.
Qed.

Lemma interrupt_holds : forall st h, holds Q st -> holds Q (interrupt_fiber st h).
Proof.
  intros st h H. unfold interrupt_fiber.
  destruct (find_fiber h (fibers st)) as [f|]; [|exact H].
  pose proof (c_interrupt _ _ HQ _ _ _ _ h H) as Hc.
  destruct (status f); try exact H;
    destruct (awaited st) as [[h' op|h' op c r]|]; unfold cleared, awaited_handle in Hc;
    try destruct (Nat.eqb h' h); exact Hc.
Qed.

Lemma run_fiber_holds : forall P E fuel ops st f,
  holds Q st -> holds Q (run_fiber pol P E fuel ops st f).
Proof.
  intros P E fuel. induction fuel as [|fuel IH]; intros ops st f H; cbn [run_fiber].
  - exact H.
  - destruct (finished st); [exact H|].
    destruct ops as [|ops]; [exact H|].
    destruct (observe (code f)) as [r|t|X e k].
    + exact H.
    + apply IH; exact H.
    + destruct e as [| | kind idx | kind args | d | | target | | r | r v].
      * apply IH. apply emit_holds; [split; [reflexivity | discriminate] | exact H].
      * apply IH. apply emit_holds; [split; [reflexivity | discriminate] | exact H].
      * destruct kind.
        -- apply IH. exact H.
        -- match goal with
           | |- holds Q (match find_fiber _ (fibers ?s) with _ => _ end) =>
               assert (H2 : holds Q s) by (apply IH; exact H);
               destruct (find_fiber _ (fibers s)); [apply IH|]; exact H2
           end.
      * destruct (awaited st) eqn:Ha.
        -- apply violate_holds; [discriminate | exact H].
        -- unfold holds in *. rewrite Ha in H. apply (c_command _ _ HQ). exact H.
      * destruct (chunk_long_sleeps pol) eqn:Hp; destruct d as [ms|];
          repeat match goal with
                 | |- context [if (?x <=? ?y) then _ else _] => destruct (x <=? y) eqn:?
                 end;
          try exact H;
          (destruct (awaited st) eqn:Ha;
           [apply violate_holds; [discriminate | exact H]
           | unfold holds in *; rewrite Ha in H; apply (c_sleep _ _ HQ); [|exact H]]);
          unfold start_ok; rewrite Hp; try exact I;
          rewrite ?Z.leb_le, ?Z.leb_gt in *;
          unfold chain_ok, max_chunk in *; repeat split;
          try (intros ? Hd; inversion Hd; subst); lia.
      * exact H.
      * match goal with
        | |- holds Q (match find_fiber _ (fibers ?s) with _ => _ end) =>
            assert (Hi : holds Q s) by (apply interrupt_holds; exact H);
            destruct (find_fiber _ (fibers s)); [apply IH|]; exact Hi
        end.
      * exact H.
      * apply IH. exact H.
      * apply IH. exact H.
Qed.

Lemma fold_interrupt_holds : forall fs st,
  holds Q st -> holds Q (fold_left (fun s f => interrupt_fiber s (handle f)) fs st).
Proof.
  intros fs. induction fs as [|f fs IH]; intros st H; [exact H|].
  apply IH. apply interrupt_holds. exact H.
Qed.

Lemma end_attempt_holds : forall st how, holds Q st -> holds Q (end_attempt st how).
Proof.
  intros st [|] H; apply finish_holds; [apply fold_interrupt_holds|]; exact H.
Qed.

Lemma tick_holds : forall st b, holds Q st -> holds Q (tick st b).
Proof. intros st b H. exact H. Qed.

Lemma run_head_holds : forall P E st h rest,
  holds Q st -> holds Q (run_head pol P E st h rest).
Proof.
  intros P E st h rest H. unfold run_head.
  destruct (find_fiber _ _) as [f|]; [|exact H].
  destruct (status f); apply tick_holds; [apply run_fiber_holds | | | |]; exact H.
Qed.

Lemma init_holds : forall P E, (forall l, Q [] None 0%nat l) -> holds Q (initial P E).
Proof.
  intros P E H0. unfold holds. cbn.
  apply (c_quiet _ _ HQ [SampleCommand 0%nat]); [split; [reflexivity | discriminate]|].
  apply (c_quiet _ _ HQ []); [split; [reflexivity | discriminate]|].
  apply H0.
Qed.

Section Turn.

Hypothesis HT : closed_turn Q.

Lemma take_sample_holds : forall E st aw floor,
  holds Q st -> awaited st = Some aw -> floor_ok aw floor ->
  holds Q (take_sample E st floor).
Proof.
  intros E st aw floor H Ha Hf. unfold holds in *. cbn -[next_logical].
  rewrite Ha in *. apply (c_sample _ HT); assumption.
Qed.

Lemma take_sample_awaited : forall E st floor,
  awaited (take_sample E st floor) = awaited st.
Proof. reflexivity. Qed.

Lemma resume_holds : forall st aw o h o',
  holds Q st -> awaited st = Some aw ->
  holds Q (resume (emit st (Delivered (awaited_op aw) (awaited_handle aw) o)) h o').
Proof.
  intros st aw o h o' H Ha. unfold resume.
  destruct (find_fiber _ _) as [f|].
  - unfold holds in *. cbn. rewrite Ha in H. apply (c_deliver _ HT). exact H.
  - apply emit_holds; [split; [reflexivity | discriminate] | exact H].
Qed.

Lemma cancel_holds : forall E st aw op h,
  holds Q st -> awaited st = Some aw ->
  holds Q (interrupt_fiber (emit (take_sample E st 0) (CancelDelivered op h)) h).
Proof.
  intros E st aw op h H Ha. apply interrupt_holds. apply emit_holds.
  - split; [reflexivity | discriminate].
  - apply take_sample_holds with aw; [exact H | exact Ha | left; reflexivity].
Qed.

(** The state after [deliver] starts the next link of a sleep chain. *)
Definition linked (st : State) (h : nat) (c : Z) (r : Chain) : State :=
  let op := next_op st in
  let st2 := emit st (SleepCommand op h c) in
  update st2 (fibers st2) (queue st2) (Some (AwaitSleep h op c r)) (abandoned st2)
    (S op) (next_sample st2) (next_handle st2) (draws st2) (logical st2)
    (trace st2) (finished st2).

Lemma linked_holds : forall st h op c r c' r',
  holds Q st -> awaited st = Some (AwaitSleep h op c r) -> next_link r = Some (c', r') ->
  holds Q (linked st h c' r').
Proof.
  intros st h op c r c' r' H Ha Hn. unfold holds in *. cbn.
  rewrite Ha in H. apply (c_link _ HT _ _ _ _ _ _ _ _ _ Hn H).
Qed.

Lemma deliver_holds : forall E st aw,
  holds Q st -> awaited st = Some aw -> holds Q (deliver E st aw).
Proof.
  intros E st aw H Ha. destruct aw as [h op|h op c r]; unfold deliver.
  - destruct (cancelled_at E op); [eapply cancel_holds; eassumption|].
    apply resume_holds with (aw := AwaitOp h op).
    + apply take_sample_holds with (AwaitOp h op); [exact H | exact Ha | left; reflexivity].
    + exact Ha.
  - destruct (cancelled_at E op); [eapply cancel_holds; eassumption|].
    assert (Hs : holds Q (take_sample E st c)).
    { apply take_sample_holds with (AwaitSleep h op c r); [exact H | exact Ha |].
      right. exists h, op, r. reflexivity. }
    pose proof (linked_holds (take_sample E st c) h op c r) as Hl.
    rewrite take_sample_awaited in Hl.
    destruct r as [|d|].
    + apply resume_holds with (aw := AwaitSleep h op c NoChain); [exact Hs | exact Ha].
    + destruct (d <=? max_chunk) eqn:Hd; refine (Hl _ _ Hs Ha _); cbn; rewrite Hd;
        reflexivity.
    + exact (Hl _ _ Hs Ha eq_refl).
Qed.

End Turn.

End Generic.
