(** * Reachable-state invariants over the awaited operation and the abandoned list, for S11.

    A predicate over [(awaited, next_op, abandoned)] that is closed under the four ways the
    executor changes them (abandoning the awaited operation, starting an await, clearing it,
    and linking a sleep chain) holds in every state a step reaches. Separately, the awaited
    fiber is always in the fiber table ([J], from S8UpperLemmas.v), so a delivery never finds
    its fiber missing. *)

From Coq Require Import List ZArith Bool Arith Lia.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model Executor Statements ExecutorLemmas S8UpperLemmas.
Import ListNotations.

Definition Pred := option Awaited -> nat -> list nat -> Prop.

Definition hold (Q : Pred) (st : State) : Prop :=
  Q (awaited st) (next_op st) (abandoned st).

Record closedA (Q : Pred) : Prop := {
  a_abandon : forall aw n ab, Q (Some aw) n ab -> Q None n (awaited_op aw :: ab);
  a_start : forall aw n ab, awaited_op aw = n -> Q None n ab -> Q (Some aw) (S n) ab;
  a_clear : forall aw n ab, Q (Some aw) n ab -> Q None n ab;
  a_link : forall aw aw' n ab, awaited_op aw' = n -> Q (Some aw) n ab -> Q (Some aw') (S n) ab
}.

Section Generic.

Variable Q : Pred.
Hypothesis HQ : closedA Q.

Lemma hold_tick : forall st b, hold Q st -> hold Q (tick st b).
Proof. intros st b H. exact H. Qed.

Lemma interrupt_hold : forall st h, hold Q st -> hold Q (interrupt_fiber st h).
Proof.
  intros st h H. unfold interrupt_fiber.
  destruct (find_fiber h (fibers st)) as [f|]; [|exact H].
  unfold hold in *.
  destruct (status f); try exact H;
    destruct (awaited st) as [[h' op|h' op c r]|] eqn:Ha; try (destruct (Nat.eqb h' h));
    cbn [awaited next_op abandoned update emit];
    first [ exact (a_abandon _ HQ (AwaitOp h' op) _ _ H)
          | exact (a_abandon _ HQ (AwaitSleep h' op c r) _ _ H)
          | exact H ].
Qed.

Lemma fold_interrupt_hold : forall fs st, hold Q st ->
  hold Q (fold_left (fun s f => interrupt_fiber s (handle f)) fs st).
Proof.
  induction fs as [|f fs IH]; intros st H; [exact H|].
  simpl. apply IH. apply interrupt_hold. exact H.
Qed.

Lemma end_attempt_hold : forall st how, hold Q st -> hold Q (end_attempt st how).
Proof.
  intros st [] H; unfold end_attempt; [|exact H].
  apply (fold_interrupt_hold _ st H).
Qed.

Lemma run_fiber_hold : forall pol P E fuel ops st f,
  hold Q st -> hold Q (run_fiber pol P E fuel ops st f).
Proof.
  intros pol P E. induction fuel as [|fuel IH]; intros ops st f H; [exact H|].
  cbn -[update emit with_fibers put_fiber set_code find_fiber new_fiber
        interrupt_fiber violate max_ops].
  destruct (finished st); [exact H|].
  destruct ops as [|ops]; [exact H|].
  destruct (observe (code f)) as [r|t|X e k]; [exact H|apply IH; exact H|].
  destruct e;
    cbn -[update emit with_fibers put_fiber set_code find_fiber new_fiber
          interrupt_fiber violate max_ops].
  - apply IH. exact H.
  - apply IH. exact H.
  - destruct f0.
    + apply IH. exact H.
    + match goal with |- context [run_fiber pol P E fuel max_ops ?A ?c] =>
        assert (Hc : hold Q (run_fiber pol P E fuel max_ops A c)) by (apply IH; exact H)
      end.
      match goal with |- context [find_fiber ?hd (fibers ?B)] =>
        destruct (find_fiber hd (fibers B)) end; [apply IH|]; exact Hc.
  - unfold hold in *. destruct (awaited st) eqn:Ha; [rewrite <- Ha in H; exact H|].
    exact (a_start _ HQ (AwaitOp (handle f) (next_op st)) _ _ eq_refl H).
  - unfold hold in *.
    destruct (chunk_long_sleeps pol), d as [ms|];
      try destruct (ms <=? 0)%Z; try destruct (ms <=? max_chunk)%Z;
      try destruct (ms <=? max_safe)%Z; try destruct (awaited st) eqn:Ha;
      first [ exact H
            | rewrite <- Ha in H; exact H
            | exact (a_start _ HQ (AwaitSleep (handle f) (next_op st) _ _) _ _ eq_refl H) ].
  - exact H.
  - match goal with |- context [interrupt_fiber ?A n] =>
      assert (Hi : hold Q (interrupt_fiber A n)) by (apply interrupt_hold; exact H) end.
    match goal with |- context [find_fiber ?hd (fibers ?B)] =>
      destruct (find_fiber hd (fibers B)) end; [apply IH|]; exact Hi.
  - exact H.
  - apply IH. exact H.
  - apply IH. exact H.
Qed.

Lemma deliver_hold : forall E st aw,
  hold Q st -> awaited st = Some aw -> hold Q (deliver E st aw).
Proof.
  intros E st aw H0 Ha. pose proof H0 as H. unfold hold in H. rewrite Ha in H.
  unfold deliver, cancel, resume.
  destruct aw as [h op|h op c r]; destruct (cancelled_at E op);
    try destruct r as [|d|]; try destruct (d <=? max_chunk)%Z;
    try (apply interrupt_hold; exact (a_clear _ HQ _ _ _ H));
    try (match goal with |- context [find_fiber ?hd (fibers ?B)] =>
           destruct (find_fiber hd (fibers B)) end;
         [exact (a_clear _ HQ _ _ _ H) | exact H0]);
    exact (a_link _ HQ _ (AwaitSleep h _ _ _) _ _ eq_refl H).
Qed.

Lemma run_head_hold : forall pol P E st h rest,
  hold Q st -> hold Q (run_head pol P E st h rest).
Proof.
  intros pol P E st h rest H. unfold run_head. cbn zeta.
  match goal with |- context [find_fiber h (fibers ?B)] =>
    destruct (find_fiber h (fibers B)) as [f|] end; [destruct (status f)|];
    apply hold_tick; try exact H. apply run_fiber_hold. exact H.
Qed.

Lemma step_hold : forall pol P E A st,
  hold Q st -> hold Q (step pol P E A no_outside_resumes st).
Proof.
  intros pol P E A st H. unfold step.
  destruct (finished st); [exact H|].
  change (no_outside_resumes _) with (@None (nat * nat)). cbv iota.
  destruct (ends_at E) as [[n how]|];
    [destruct (Nat.eqb n (progress st));
     [apply hold_tick, end_attempt_hold; exact H|]|];
    (destruct (queue st) as [|h rest]; [|apply run_head_hold; exact H]);
    (destruct (awaited st) as [aw|] eqn:Ha;
     [ destruct (A (awaited_op aw) (micro st));
       [apply hold_tick, deliver_hold; [exact H|exact Ha] | exact H]
     | destruct (root_done st); [|destruct (blocked_is_violation pol)]; exact H ]).
Qed.

Lemma iterate_hold : forall pol P E A n st,
  hold Q st -> hold Q (iterate pol P E A no_outside_resumes n st).
Proof.
  intros pol P E A n. induction n as [|n IH]; intros st H; [exact H|].
  simpl. apply IH. apply step_hold. exact H.
Qed.

End Generic.

Lemma iterate_add : forall pol P E A X a b st,
  iterate pol P E A X (a + b) st = iterate pol P E A X b (iterate pol P E A X a st).
Proof.
  intros pol P E A X a. induction a as [|a IH]; intros b st; [reflexivity|].
  simpl. apply IH.
Qed.

(** ** The predicates *)

(** An awaited operation has been issued and is not abandoned; every abandoned operation has
    been issued. *)
Definition Inv0 : Pred := fun aw n ab =>
  (forall a, aw = Some a -> (awaited_op a < n)%nat /\ ~ In (awaited_op a) ab) /\
  (forall x, In x ab -> (x < n)%nat).

(** Operation [op] has been issued, is not abandoned and is not awaited: after its delivery. *)
Definition After (op : nat) : Pred := fun aw n ab =>
  (op < n)%nat /\ ~ In op ab /\ (forall a, aw = Some a -> awaited_op a <> op).

(** Operation [op] is abandoned. *)
Definition Has (op : nat) : Pred := fun _ _ ab => In op ab.

Lemma Inv0_closed : closedA Inv0.
Proof.
  split; unfold Inv0.
  - intros aw n ab [H1 H2]. destruct (H1 aw eq_refl) as [Hlt _].
    split; [intros a Ha; discriminate|]. intros x [<-|Hx]; [exact Hlt|exact (H2 x Hx)].
  - intros aw n ab Hn [_ H2]. split.
    + intros a Ha. injection Ha as <-. rewrite Hn. split; [lia|].
      intros Hin. specialize (H2 _ Hin). lia.
    + intros x Hx. specialize (H2 x Hx). lia.
  - intros aw n ab [_ H2]. split; [intros a Ha; discriminate|exact H2].
  - intros aw aw' n ab Hn [_ H2]. split.
    + intros a Ha. injection Ha as <-. rewrite Hn. split; [lia|].
      intros Hin. specialize (H2 _ Hin). lia.
    + intros x Hx. specialize (H2 x Hx). lia.
Qed.

Lemma After_closed : forall op, closedA (After op).
Proof.
  intros op. split; unfold After.
  - intros aw n ab (H1 & H2 & H3). split; [exact H1|]. split; [|intros a Ha; discriminate].
    intros [Heq|Hin]; [exact (H3 aw eq_refl Heq)|exact (H2 Hin)].
  - intros aw n ab Hn (H1 & H2 & _). split; [lia|]. split; [exact H2|].
    intros a Ha. injection Ha as <-. lia.
  - intros aw n ab (H1 & H2 & _). split; [exact H1|]. split; [exact H2|].
    intros a Ha; discriminate.
  - intros aw aw' n ab Hn (H1 & H2 & _). split; [lia|]. split; [exact H2|].
    intros a Ha. injection Ha as <-. lia.
Qed.

Lemma Has_closed : forall op, closedA (Has op).
Proof.
  intros op. split; unfold Has; intros; simpl; auto.
Qed.

(** ** The awaited fiber is in the fiber table *)

Lemma J_tick : forall st b, J st -> J (tick st b).
Proof. intros st b H. exact H. Qed.

Lemma deliver_J : forall E st aw, J st -> awaited st = Some aw -> J (deliver E st aw).
Proof.
  intros E st aw H Ha. unfold deliver, cancel, resume.
  destruct aw as [h op|h op c r]; destruct (cancelled_at E op);
    try destruct r as [|d|]; try destruct (d <=? max_chunk)%Z;
    try (apply (proj1 (interrupt_frame _ h)); intros a Hb; discriminate);
    try (match goal with |- context [find_fiber ?hd (fibers ?B)] =>
           destruct (find_fiber hd (fibers B)) end;
         [intros a Hb; discriminate | exact H]);
    intros a Hb; cbn in Hb; injection Hb as <-; exact (H _ Ha).
Qed.

Lemma run_head_J : forall pol P E st h rest, J st -> J (run_head pol P E st h rest).
Proof.
  intros pol P E st h rest H. unfold run_head. cbn zeta.
  match goal with |- context [find_fiber h (fibers ?B)] =>
    destruct (find_fiber h (fibers B)) as [f|] eqn:Hf end; [destruct (status f)|];
    apply J_tick; try exact H.
  apply (proj1 (run_fiber_frame _ _ _ _ _ _ f (proj1 (find_fiber_in _ _ _ Hf)))). exact H.
Qed.

Lemma step_J : forall pol P E A st, J st -> J (step pol P E A no_outside_resumes st).
Proof.
  intros pol P E A st H. unfold step.
  destruct (finished st); [exact H|].
  change (no_outside_resumes _) with (@None (nat * nat)). cbv iota.
  destruct (ends_at E) as [[n how]|];
    [destruct (Nat.eqb n (progress st));
     [apply J_tick, (proj1 (end_attempt_frame st how)); exact H|]|];
    (destruct (queue st) as [|h rest]; [|apply run_head_J; exact H]);
    (destruct (awaited st) as [aw|] eqn:Ha;
     [ destruct (A (awaited_op aw) (micro st));
       [apply J_tick, deliver_J; [exact H|exact Ha] | exact H]
     | destruct (root_done st); [|destruct (blocked_is_violation pol)]; exact H ]).
Qed.

Lemma iterate_J : forall pol P E A n st,
  J st -> J (iterate pol P E A no_outside_resumes n st).
Proof.
  intros pol P E A n. induction n as [|n IH]; intros st H; [exact H|].
  simpl. apply IH, step_J. exact H.
Qed.

Lemma reachable_J : forall pol P E A n,
  J (iterate pol P E A no_outside_resumes n (initial P E)).
Proof. intros pol P E A n. apply iterate_J. intros a Ha. discriminate. Qed.
