(** * S8_upper: [L] is bounded by true time, the host error and a lead per sleep.

    The invariant is the bound with the awaited sleep's lead kept back. The sleep command adds
    a lead to the bound when it is issued; the completion of its chunk spends it, because [L]
    gains the whole chunk while true time may gain the chunk less the lead. A cancelled sleep
    spends nothing. A delivery always resumes the awaited fiber, which is in the fiber table,
    so a chunk is delivered once. *)

From Coq Require Import List ZArith Bool Arith Lia.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model Executor Statements SingleStepLemmas
  SingleStepInvariants ExecutorLemmas S8UpperLemmas.
Import ListNotations.
Open Scope Z_scope.

Section Upper.

Variable P : Program.
Variable E : Env.
Variable A : Arrival.
Variables emax lead : Z.
Hypothesis Hmono :
  forall i j, (i <= j)%nat -> true_time (sample_of E i) <= true_time (sample_of E j).
Hypothesis Herr : forall i, host_error (sample_of E i) <= emax.
Hypothesis Hlead : 0 <= lead.

(** The bound before the lead per sleep, for sample index [ns]. *)
Definition bound (ns : nat) : Z := true_time (sample_of E (pred ns)) + emax.

Definition Inv8 (st : State) : Prop :=
  J st /\ holds (U lead (bound (next_sample st))) st.

Lemma inv8_frame : forall st r,
  Inv8 st -> Frame st r -> holds (U lead (bound (next_sample st))) r -> Inv8 r.
Proof.
  intros st r [HJ _] (HF & Hn & _) HU. split; [exact (HF HJ)|]. rewrite Hn. exact HU.
Qed.

Lemma inv8_tick : forall st b, Inv8 st -> Inv8 (tick st b).
Proof. intros st b H. exact H. Qed.

Lemma inv8_interrupt : forall st h, Inv8 st -> Inv8 (interrupt_fiber st h).
Proof.
  intros st h H. apply inv8_frame with st; [exact H | apply interrupt_frame|].
  apply (interrupt_holds _ _ (U_closed _ _ Hlead)). exact (proj2 H).
Qed.

Lemma inv8_finish : forall st e, Inv8 st -> Inv8 (finish st e).
Proof.
  intros st e H. apply inv8_frame with st; [exact H | apply frame_same; reflexivity|].
  apply (finish_holds _ _ (U_closed _ _ Hlead)). exact (proj2 H).
Qed.

Lemma inv8_violate : forall st v,
  v <> StepOutsideTurn -> Inv8 st -> Inv8 (violate st v).
Proof.
  intros st v Hv H. apply inv8_frame with st; [exact H | apply frame_same; reflexivity|].
  apply (violate_holds _ _ (U_closed _ _ Hlead)); [exact Hv | exact (proj2 H)].
Qed.

Lemma inv8_end_attempt : forall st how, Inv8 st -> Inv8 (end_attempt st how).
Proof.
  intros st how H. apply inv8_frame with st; [exact H | apply end_attempt_frame|].
  apply (end_attempt_holds _ _ (U_closed _ _ Hlead)). exact (proj2 H).
Qed.

Lemma inv8_run_head : forall st h rest, Inv8 st -> Inv8 (run_head policy_v1 P E st h rest).
Proof.
  intros st h rest H. unfold run_head. cbn zeta.
  match goal with |- Inv8 (match find_fiber h (fibers ?B) with _ => _ end) =>
    assert (H0 : Inv8 B) by exact H;
    destruct (find_fiber h (fibers B)) as [f|] eqn:Hf end;
    [destruct (status f)|]; apply inv8_tick; try exact H0.
  match goal with |- Inv8 (run_fiber ?a ?b ?c ?d ?e ?s ?g) =>
    pose proof (run_fiber_frame a b c d e s g (proj1 (find_fiber_in _ _ _ Hf))) as HF;
    pose proof (run_fiber_holds _ _ (U_closed lead (bound (next_sample s)) Hlead)
      b c d e s g (proj2 H0)) as HU;
    remember (run_fiber a b c d e s g) as r eqn:Er; clear Er end.
  exact (inv8_frame _ _ H0 HF HU).
Qed.

(** ** Delivery *)

Lemma sleeps_sample : forall tr i s,
  sleep_commands ((tr ++ [SampleCommand i]) ++ [Sampled i s]) = sleep_commands tr.
Proof. intros tr i s. rewrite !sleeps_snoc. cbn. lia. Qed.

(** The facts a delivery's arithmetic needs. *)
Lemma delivery_facts : forall st,
  bound (next_sample st) <= bound (S (next_sample st)) /\
  sample_value (sample_of E (next_sample st)) <= bound (S (next_sample st)).
Proof.
  intros st. unfold bound, sample_value. cbn [pred]. split.
  - pose proof (Hmono (pred (next_sample st)) (next_sample st) (Nat.le_pred_l _)). lia.
  - pose proof (Herr (next_sample st)). lia.
Qed.

(** A sample with no floor, then an action that is not a sleep command. *)
Lemma inv8_sample : forall st aw a,
  Inv8 st -> awaited st = Some aw -> is_sleep a = false ->
  Inv8 (emit (take_sample E st 0) a).
Proof.
  intros st aw a [HJ [H1 H2]] Ha Hs. split; [exact HJ|].
  destruct (delivery_facts st) as [HT HS].
  destruct (lead_products lead (sleep_commands (trace st)) Hlead) as (Hx & Hx1 & _).
  unfold holds, U. cbn -[sleep_commands bound sample_value].
  rewrite sleeps_snoc, sleeps_sample, Hs, Nat.add_0_r. rewrite Ha in *.
  split; [|exact H2].
  unfold next_logical. destruct aw as [h op|h op c r]; cbn [reserve] in *; [lia|].
  specialize (Hx1 (H2 _ _ _ _ eq_refl)). lia.
Qed.

(** A resume clears the awaited operation; [L] needs only the bound with nothing kept back. *)
Lemma inv8_resume : forall s h o,
  In h (hs s) ->
  logical s <= bound (next_sample s) + Z.of_nat (sleep_commands (trace s)) * lead ->
  Inv8 (resume s h o).
Proof.
  intros s h o Hin Hl. unfold resume.
  destruct (find_fiber h (fibers s)) as [f|] eqn:Hf;
    [|destruct (find_fiber_none _ _ Hin Hf)].
  split; [intros aw Haw; discriminate|]. unfold holds, U.
  cbn [update logical next_sample trace awaited reserve].
  split; [lia | intros; discriminate].
Qed.

(** Clearing the awaited operation, as a delivered cancellation does, keeps the invariant:
    the lead held back for an awaited sleep is released. *)
Lemma inv8_clear : forall s, Inv8 s ->
  Inv8 (update s (fibers s) (queue s) None (abandoned s) (next_op s) (next_sample s)
          (next_handle s) (draws s) (logical s) (trace s) (finished s)).
Proof.
  intros s [_ [H1 _]]. split; [intros aw Haw; discriminate|].
  unfold holds, U. cbn [update logical next_sample trace awaited reserve].
  destruct (reserve_range lead (awaited s) Hlead) as [Hr|Hr]; rewrite Hr in H1;
    (split; [lia | intros; discriminate]).
Qed.

Lemma inv8_deliver_op : forall st h op,
  Inv8 st -> awaited st = Some (AwaitOp h op) -> Inv8 (deliver E st (AwaitOp h op)).
Proof.
  intros st h op H Ha. unfold deliver.
  destruct (cancelled_at E op).
  - unfold cancel. apply inv8_interrupt, inv8_clear.
    apply inv8_sample with (AwaitOp h op); auto.
  - destruct (inv8_sample st _ (Delivered op h (Some (outcome_of E op))) H Ha eq_refl)
      as [_ [Hb _]].
    apply inv8_resume; [exact (proj1 H _ Ha)|].
    revert Hb. unfold holds, U.
    cbn -[sleep_commands bound sample_value next_logical]. rewrite Ha. cbn [reserve]. lia.
Qed.

(** After a completed chunk, [L] is within the bound at the new sample, with no lead kept. *)
Lemma chunk_bound : forall st h op c r,
  Inv8 st -> awaited st = Some (AwaitSleep h op c r) ->
  true_time (sample_of E (next_sample st))
    >= true_time (sample_of E (pred (next_sample st))) + c - lead ->
  next_logical (logical st) c (sample_value (sample_of E (next_sample st)))
    <= bound (S (next_sample st)) + Z.of_nat (sleep_commands (trace st)) * lead.
Proof.
  intros st h op c r [_ [H1 _]] Ha Hc. rewrite Ha in H1. cbn [reserve] in H1.
  destruct (delivery_facts st) as [_ HS].
  destruct (lead_products lead (sleep_commands (trace st)) Hlead) as (Hx & _ & _).
  unfold next_logical. unfold bound in *. cbn [pred] in *. lia.
Qed.

Lemma inv8_link : forall st h op c r c' r',
  Inv8 st -> awaited st = Some (AwaitSleep h op c r) ->
  next_logical (logical st) c (sample_value (sample_of E (next_sample st)))
    <= bound (S (next_sample st)) + Z.of_nat (sleep_commands (trace st)) * lead ->
  Inv8 (linked (take_sample E st c) h c' r').
Proof.
  intros st h op c r c' r' H Ha Hb. split.
  - intros aw Haw. injection Haw as <-. exact (proj1 H _ Ha).
  - destruct (lead_products lead (sleep_commands (trace st)) Hlead) as (_ & _ & Hp).
    unfold holds, U. cbn -[sleep_commands bound sample_value next_logical].
    rewrite sleeps_snoc, sleeps_sample. cbn [is_sleep reserve].
    split; [rewrite Hp; lia | intros; lia].
Qed.

Lemma inv8_deliver_sleep : forall st h op c r,
  Inv8 st -> awaited st = Some (AwaitSleep h op c r) ->
  true_time (sample_of E (next_sample st))
    >= true_time (sample_of E (pred (next_sample st))) + c - lead ->
  Inv8 (deliver E st (AwaitSleep h op c r)).
Proof.
  intros st h op c r H Ha Hc. unfold deliver.
  destruct (cancelled_at E op).
  { unfold cancel. apply inv8_interrupt, inv8_clear.
    apply inv8_sample with (AwaitSleep h op c r); auto. }
  pose proof (chunk_bound _ _ _ _ _ H Ha Hc) as Hb.
  pose proof (inv8_link st h op c r) as Hl.
  destruct r as [|d|].
  - apply inv8_resume; [exact (proj1 H _ Ha)|].
    cbn -[sleep_commands bound sample_value next_logical].
    rewrite sleeps_snoc, sleeps_sample, Nat.add_0_r. exact Hb.
  - destruct (d <=? max_chunk); apply (Hl _ _ H Ha Hb).
  - apply (Hl _ _ H Ha Hb).
Qed.

(** ** A micro-step, and every reachable state *)

Lemma inv8_turn : forall st,
  Inv8 st ->
  (forall h op c r, awaited st = Some (AwaitSleep h op c r) ->
     true_time (sample_of E (next_sample st))
       >= true_time (sample_of E (pred (next_sample st))) + c - lead) ->
  Inv8 (turn policy_v1 P E A st).
Proof.
  intros st H Hc. unfold turn.
  destruct (queue st) as [|h rest]; [|apply inv8_run_head; exact H].
  destruct (awaited st) as [aw|] eqn:Ha.
  - destruct (A _ _); apply inv8_tick; [|exact H].
    destruct aw as [h op|h op c r];
      [apply inv8_deliver_op | apply inv8_deliver_sleep];
      try exact (Hc _ _ _ _ eq_refl); auto.
  - destruct (root_done st); apply inv8_tick;
      [apply inv8_finish | apply inv8_violate; [discriminate|]]; exact H.
Qed.

Lemma inv8_step : forall st,
  Inv8 st ->
  (forall h op c r, awaited st = Some (AwaitSleep h op c r) ->
     true_time (sample_of E (next_sample st))
       >= true_time (sample_of E (pred (next_sample st))) + c - lead) ->
  Inv8 (step policy_v1 P E A no_outside_resumes st).
Proof.
  intros st H Hc. destruct (finished st) as [e|] eqn:Hf.
  - rewrite (step_finished _ _ _ _ _ _ e Hf). exact H.
  - rewrite step_unfold by (exact Hf || reflexivity).
    destruct (ends_at E) as [[n how]|];
      [destruct (Nat.eqb n (progress st))|]; try (apply inv8_turn; assumption).
    apply inv8_tick. apply inv8_end_attempt. exact H.
Qed.

Lemma inv8_initial : Inv8 (initial P E).
Proof.
  split; [intros aw Haw; discriminate|].
  unfold holds, U, bound, sample_value. cbn [reserve pred initial trace awaited logical
    next_sample sleep_commands filter length].
  unfold sample_value. pose proof (Herr 0). split; [lia | intros; discriminate].
Qed.

End Upper.

Theorem s8_upper : S8_upper.
Proof.
  intros P E A emax lead Hmono Herr Hlead Hc k. cbv zeta.
  assert (H : Inv8 E emax lead
    (iterate policy_v1 P E A no_outside_resumes k (initial P E))).
  { induction k as [|k IH]; [apply inv8_initial; assumption|].
    rewrite iterate_S. apply inv8_step; try assumption. exact (Hc k). }
  destruct H as [_ [H1 _]]. unfold bound in H1.
  match goal with H1 : logical ?s + reserve lead ?a <= _ |- _ =>
    destruct (reserve_range lead a Hlead) as [Hr|Hr]; rewrite Hr in H1 end; lia.
Qed.
