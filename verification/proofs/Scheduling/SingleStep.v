(** * Proofs of the single-step statements S4, S5, S6, S7 and four parts of S8. *)

From Coq Require Import List ZArith Bool Arith Lia.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model Executor Statements SingleStepLemmas
  SingleStepInvariants.
Import ListNotations.
Open Scope Z_scope.

(** ** Two more closed properties: the trace extends a fixed prefix, and [L] is fixed *)

Definition Pre (T0 : list Action) : Inv := fun tr _ _ _ => exists rest, tr = T0 ++ rest.

Lemma Pre_snoc : forall (T0 tr : list Action) (a : Action), (exists rest, tr = T0 ++ rest) ->
  exists rest, tr ++ [a] = T0 ++ rest.
Proof. intros T0 tr a [rest ->]. exists (rest ++ [a]). rewrite app_assoc. reflexivity. Qed.

Lemma Pre_closed : forall pol T0, closed pol (Pre T0).
Proof.
  intros pol T0. split; intros; apply Pre_snoc; assumption.
Qed.

Definition Lfix (L0 : Z) : Inv := fun _ _ _ l => l = L0.

Lemma Lfix_closed : forall pol L0, closed pol (Lfix L0).
Proof. intros pol L0. split; intros; assumption. Qed.

Lemma interrupt_trace : forall st h T0,
  (exists rest, trace st = T0 ++ rest) ->
  exists rest, trace (interrupt_fiber st h) = T0 ++ rest.
Proof.
  intros st h T0 H. exact (interrupt_holds policy_v1 (Pre T0) (Pre_closed _ _) st h H).
Qed.

Lemma interrupt_logical : forall st h, logical (interrupt_fiber st h) = logical st.
Proof.
  intros st h.
  exact (interrupt_holds _ (Lfix (logical st)) (Lfix_closed policy_v1 _) st h eq_refl).
Qed.

(** ** Reducing a micro-step at a turn boundary *)

Lemma step_turn : forall pol P E A st,
  finished st = None ->
  (forall n how, ends_at E = Some (n, how) -> n <> progress st) ->
  step pol P E A no_outside_resumes st = turn pol P E A st.
Proof.
  intros pol P E A st Hf Hend. rewrite step_unfold by (exact Hf || reflexivity).
  destruct (ends_at E) as [[n how]|] eqn:He; [|reflexivity].
  destruct (Nat.eqb n (progress st)) eqn:En; [|reflexivity].
  apply Nat.eqb_eq in En. destruct (Hend n how eq_refl En).
Qed.

Lemma step_deliver : forall pol P E A st aw,
  finished st = None -> queue st = [] -> awaited st = Some aw ->
  A (awaited_op aw) (micro st) = true ->
  (forall n how, ends_at E = Some (n, how) -> n <> progress st) ->
  step pol P E A no_outside_resumes st = tick (deliver E st aw) true.
Proof.
  intros pol P E A st aw Hf Hq Ha HA Hend. rewrite step_turn by assumption.
  unfold turn. rewrite Hq, Ha, HA. reflexivity.
Qed.

(** A delivery's first action is its sample command. *)
Lemma deliver_trace : forall E st aw,
  exists rest, trace (deliver E st aw) = trace st ++ SampleCommand (next_sample st) :: rest.
Proof.
  intros E st aw.
  assert (H : exists rest, trace (deliver E st aw)
                = (trace st ++ [SampleCommand (next_sample st)]) ++ rest).
  { destruct aw as [h op|h op c r]; unfold deliver;
      destruct (cancelled_at E op);
      try (apply interrupt_trace; cbn; eexists; rewrite <- !app_assoc; reflexivity).
    - unfold resume. destruct (find_fiber _ _); cbn; eexists; rewrite <- !app_assoc;
        reflexivity.
    - destruct r as [|d|]; [unfold resume; destruct (find_fiber _ _)
                            | destruct (d <=? max_chunk) | ];
        cbn; eexists; rewrite <- !app_assoc; reflexivity. }
  destruct H as [rest H]. exists rest. rewrite H, <- app_assoc. reflexivity.
Qed.

(** ** S4 *)

Theorem s4 : S4.
Proof.
  intros P E A n. unfold run. exact (proj1 (reachable_W policy_v1 P E A n)).
Qed.

(** ** S5 *)

(** Once the outside-resume violation is in the trace, it and the defect end the trace, and
    the attempt has finished. *)
Definition ends_detected (st : State) : Prop :=
  In (Violated StepOutsideTurn) (trace st) ->
  (exists before, trace st = before ++ [Violated StepOutsideTurn; Exited Defect]) /\
  finished st <> None.

Lemma step_ends_detected : forall P E A X st,
  ends_detected st -> ends_detected (step policy_v1 P E A X st).
Proof.
  intros P E A X st H. destruct (finished st) as [e|] eqn:Hf.
  - rewrite (step_finished _ _ _ _ _ _ e Hf). exact H.
  - assert (HN : ~ In (Violated StepOutsideTurn) (trace st)).
    { intros Hin. destruct (H Hin) as [_ Hd]. exact (Hd Hf). }
    destruct (X (micro st)) as [[h v]|] eqn:Hx.
    + unfold step. rewrite Hf, Hx.
      destruct (find_fiber h (fibers st)) as [f|]; [destruct (status f)|];
        try (intros Hin; destruct (HN Hin)).
      intros _. split; [|cbn; discriminate].
      exists (trace st). cbn. rewrite <- app_assoc. reflexivity.
    + rewrite step_no_resume by exact Hx.
      pose proof (step_holds _ _ (N_closed policy_v1) N_closed_turn P E A st HN) as Hs.
      intros Hin. destruct (Hs Hin).
Qed.

Lemma iterate_ends_detected : forall P E A X k st,
  ends_detected st -> ends_detected (iterate policy_v1 P E A X k st).
Proof.
  intros P E A X k. induction k as [|k IH]; intros st H; [exact H|].
  apply IH. apply step_ends_detected. exact H.
Qed.

Theorem s5 : S5.
Proof.
  intros P E A X n Hin. unfold run_with in *.
  apply iterate_ends_detected; [|exact Hin].
  intros H0. cbn in H0. destruct H0 as [H0|[H0|[]]]; discriminate.
Qed.

Theorem s5_detects : S5_detects.
Proof.
  intros pol P E A X k h v f st Hf Hx Hfind Hs. unfold step.
  rewrite Hf, Hx, Hfind, Hs. cbn.
  apply in_or_app. left. apply in_or_app. right. left. reflexivity.
Qed.

(** ** S6 *)

Theorem s6 : S6.
Proof.
  intros P E A A' k st Hf Hq Ha Hr Hend.
  rewrite step_turn by assumption. unfold turn. rewrite Hq, Ha, Hr. cbn.
  rewrite <- app_assoc. reflexivity.
Qed.

(** ** S7 *)

Theorem s7 : S7.
Proof.
  intros P E A k aw st Hf Hq Ha HA Hend.
  rewrite (step_deliver _ _ _ _ _ aw) by assumption.
  exact (deliver_trace E st aw).
Qed.

Theorem s7_turns : S7_turns.
Proof.
  intros P E A k st st' Hf Hq Hq'. subst st'.
  rewrite step_unfold in Hq' |- * by (exact Hf || reflexivity).
  assert (Hturn : queue (turn policy_v1 P E A st) <> [] ->
    exists a rest, trace (turn policy_v1 P E A st) = trace st ++ a :: rest /\
      ((exists i, a = SampleCommand i) \/ (exists h, a = Interrupted h))).
  { unfold turn. rewrite Hq. intros Hq2. destruct (awaited st) as [aw|].
    - destruct (A (awaited_op aw) (micro st)); [|destruct Hq2; exact Hq].
      destruct (deliver_trace E st aw) as [rest Hr].
      exists (SampleCommand (next_sample st)), rest.
      split; [exact Hr | left; eexists; reflexivity].
    - destruct (root_done st); destruct Hq2; reflexivity. }
  destruct (ends_at E) as [[n how]|]; [|apply Hturn; exact Hq'].
  destruct (Nat.eqb n (progress st)); [|apply Hturn; exact Hq'].
  destruct how; destruct Hq'; reflexivity.
Qed.

(** ** S8 *)

Theorem s8_monotone : S8_monotone.
Proof.
  intros P E A k st.
  assert (H : holds (M (logical st)) st).
  { split; [exact (reachable_C P E A k) | lia]. }
  exact (proj2 (step_holds _ _ (M_closed _) (M_closed_turn _) P E A st H)).
Qed.

Lemma deliver_sleep_logical : forall E st h op chunk rest,
  cancelled_at E op = false ->
  logical (deliver E st (AwaitSleep h op chunk rest))
    = next_logical (logical st) chunk (sample_value (sample_of E (next_sample st))).
Proof.
  intros E st h op chunk rest Hc. unfold deliver. rewrite Hc.
  destruct rest as [|d|];
    [unfold resume; destruct (find_fiber _ _) | destruct (d <=? max_chunk) |];
    reflexivity.
Qed.

Theorem s8_floor : S8_floor.
Proof.
  intros P E A k h op chunk rest st st' Hf Hq Ha Hc HA Hend. subst st'.
  rewrite (step_deliver _ _ _ _ _ _ Hf Hq Ha HA Hend). cbn [logical tick].
  rewrite deliver_sleep_logical by exact Hc. unfold next_logical. lia.
Qed.

Theorem s8_cancel : S8_cancel.
Proof.
  intros P E A k h op chunk rest st st' Hf Hq Ha Hc HA Hend. subst st'.
  rewrite (step_deliver _ _ _ _ _ _ Hf Hq Ha HA Hend). cbn [logical tick].
  unfold deliver. rewrite Hc, interrupt_logical. cbn -[sample_value Z.max].
  unfold next_logical. rewrite Z.add_0_r. reflexivity.
Qed.

Theorem s8_chunks : S8_chunks.
Proof.
  intros P E A n op h d Hin. unfold run in Hin.
  exact (proj1 (reachable_C P E A n) _ _ _ Hin).
Qed.
