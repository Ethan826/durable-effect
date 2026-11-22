(** * S11, abandonment is silent.

    Two environments that differ only in an operation's outcome and cancellation take the same
    steps, except at a step that delivers that operation: no other step reads either value.
    In a run where the operation is abandoned, no step delivers it. Before such a delivery the
    operation is awaited, so it is not in the abandoned list (which only grows); after it, the
    operation is never awaited or abandoned again. *)

From Coq Require Import List ZArith Bool Arith Lia.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model Executor Statements ExecutorLemmas S8UpperLemmas
  Replay AbandonmentLemmas.
Import ListNotations.


Section Silent.

Variables (P : Program) (E1 E2 : Env) (A : Arrival) (op : nat).
Hypothesis Ho : forall n, n <> op -> outcome_of E1 n = outcome_of E2 n.
Hypothesis Hc : forall n, n <> op -> cancelled_at E1 n = cancelled_at E2 n.
Hypothesis Hs : forall n, sample_of E1 n = sample_of E2 n.
Hypothesis Hr : forall n, random_of E1 n = random_of E2 n.
Hypothesis He : ends_at E1 = ends_at E2.

(** The two environments take the same step, unless the step delivers operation [op]. *)
Lemma step_unless_delivers : forall st,
  step policy_v1 P E1 A no_outside_resumes st = step policy_v1 P E2 A no_outside_resumes st \/
  exists aw, awaited st = Some aw /\ awaited_op aw = op /\
    step policy_v1 P E1 A no_outside_resumes st = tick (deliver E1 st aw) true.
Proof.
  intros st. unfold step.
  destruct (finished st); [left; reflexivity|].
  change (no_outside_resumes _) with (@None (nat * nat)). cbv iota. rewrite He.
  destruct (ends_at E2) as [[n how]|];
    [destruct (Nat.eqb n (progress st)); [left; reflexivity|]|];
    (destruct (queue st) as [|h rest]; [|left; apply run_head_env; exact Hr]);
    (destruct (awaited st) as [aw|] eqn:Ha; [|left; reflexivity]);
    (destruct (A (awaited_op aw) (micro st)); [|left; reflexivity]);
    (destruct (Nat.eq_dec (awaited_op aw) op) as [Hop|Hop];
     [ right; exists aw; split; [reflexivity|split; [exact Hop|reflexivity]]
     | left; rewrite (deliver_env E1 E2 st aw);
       [reflexivity | apply Ho; exact Hop | apply Hc; exact Hop | apply Hs] ]).
Qed.

End Silent.

(** After a delivery of the awaited operation, it is issued, not abandoned and not awaited. *)
Lemma deliver_after : forall E st aw,
  hold Inv0 st -> J st -> awaited st = Some aw ->
  hold (After (awaited_op aw)) (deliver E st aw).
Proof.
  intros E st aw [H1 _] HJ Ha. destruct (H1 aw Ha) as [Hlt Hnin].
  assert (Hclear : After (awaited_op aw) None (next_op st) (abandoned st))
    by (split; [exact Hlt|split; [exact Hnin|intros a Hb; discriminate]]).
  unfold deliver, cancel, resume.
  destruct aw as [h o|h o c r]; destruct (cancelled_at E o);
    try destruct r as [|d|]; try destruct (d <=? max_chunk)%Z;
    cbn [awaited_op] in Hlt, Hnin, Hclear |- *;
    try (apply (interrupt_hold _ (After_closed _)); exact Hclear);
    try (match goal with |- context [find_fiber ?hd (fibers ?B)] =>
           destruct (find_fiber hd (fibers B)) eqn:Hf end;
         [ exact Hclear
         | exfalso; exact (find_fiber_none _ (fibers st) (HJ _ Ha) Hf) ]);
    (split; [cbn; lia|split; [exact Hnin|]]);
    intros a Hb; cbn in Hb; injection Hb as <-; cbn in Hlt |- *; lia.
Qed.

Lemma Inv0_initial : forall P E, hold Inv0 (initial P E).
Proof. intros P E. split; [intros a Ha; discriminate|intros x []]. Qed.

(** In a run where [op] is abandoned at step [k], no step delivers [op]. *)
Lemma no_delivery : forall P E A k op n aw,
  let R m := iterate policy_v1 P E A no_outside_resumes m (initial P E) in
  In op (abandoned (R k)) ->
  awaited (R n) = Some aw -> awaited_op aw = op ->
  step policy_v1 P E A no_outside_resumes (R n) = tick (deliver E (R n) aw) true ->
  False.
Proof.
  intros P E A k op n aw R Hk Ha Hop Hstep.
  assert (H0 : hold Inv0 (R n)) by (apply iterate_hold; [exact Inv0_closed|apply Inv0_initial]).
  destruct (Nat.le_gt_cases k n) as [Hle|Hgt].
  - assert (Hn : hold (Has op) (R n)).
    { unfold R. replace n with (k + (n - k))%nat by lia. rewrite iterate_add.
      apply iterate_hold; [apply Has_closed|exact Hk]. }
    destruct (proj1 H0 aw Ha) as [_ Hnin]. rewrite Hop in Hnin. exact (Hnin Hn).
  - assert (Ha1 : hold (After op) (R (S n))).
    { unfold R. rewrite iterate_S. fold (R n). rewrite Hstep. apply hold_tick.
      rewrite <- Hop. apply deliver_after; [exact H0|apply reachable_J|exact Ha]. }
    assert (Hk' : hold (After op) (R k)).
    { unfold R. replace k with (S n + (k - S n))%nat by lia. rewrite iterate_add.
      apply iterate_hold; [apply After_closed|exact Ha1]. }
    destruct Hk' as (_ & Hnin & _). exact (Hnin Hk).
Qed.

Theorem s11 : S11.
Proof.
  intros P E1 E2 A k op. cbv zeta. intros Hk Ho Hc Hs Hr He n. unfold run.
  f_equal. induction n as [|n IH].
  - apply initial_same. exact Hs.
  - rewrite !iterate_S, <- IH.
    destruct (step_unless_delivers P E1 E2 A op Ho Hc Hs Hr He
                (iterate policy_v1 P E1 A no_outside_resumes n (initial P E1)))
      as [H|(aw & Ha & Hop & Hstep)]; [exact H|].
    exfalso. exact (no_delivery P E1 A k op n aw Hk Ha Hop Hstep).
Qed.
