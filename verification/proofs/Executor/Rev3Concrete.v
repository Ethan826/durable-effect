(** * [MeetsConcrete]: the concrete runtime meets the interface.

    I1 holds because the runtime's equivalence is equality. I4, I6, I7 and I8 follow from the
    monitor of Rev3Monitor.v: every task keeps the invariant [Inv] of Rev3ConcreteBase.v,
    for every task sequence, including ones the executor never produces. Proofs of the rev3
    domain. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Concrete Statements Obligations.
From Durable Require Import Rev3Monitor Rev3ConcreteBase Rev3ConcreteSteps Rev3ConcreteGo.
Import ListNotations.
Open Scope nat_scope.

Lemma rev3_inv_init : forall p seed, Inv m0 (c_init p seed).
Proof.
  intros p seed. constructor; simpl; try (intros; discriminate); try tauto.
  - constructor.
  - lia.
Qed.

(** A fiber that the task runs, from its record. *)
Lemma rev3_run_record : forall fuel m s f p g,
  Inv m s -> look f s = Some p -> begun p = true -> status p <> Finished -> no_pend m f ->
  fid g = f -> begun g = true -> status g = Ready ->
  wp m (go fuel 0 s g) Inv.
Proof.
  intros fuel m s f p g H Hl Hb Hf Hn Hid Hb' Hr.
  pose proof (rev3_pre_of_record m s f p g H Hl Hb Hf Hn Hid Hb' Hr) as P.
  refine (rev3_wp_mono _ _ _ _ _ _ (proj1 (rev3_go_ok fuel) 0 s g m H P)).
  intros m' s' [Hi _]. exact Hi.
Qed.

(** A fiber's first run: its start is reported, and it runs. *)
Lemma rev3_start_record : forall fuel m s f p g b,
  Inv m s -> look f s = Some p -> begun p = false ->
  fid g = f -> begun g = true -> status g = Ready ->
  mok m (LRegister f b) /\ wp (mnext m (LRegister f b)) (go fuel 0 (put g s) g) Inv.
Proof.
  intros fuel m s f p g b H Hl Hb Hid Hb' Hr.
  split; [exact (rev3_mok_register_record m s f p b H Hl Hb)|].
  pose proof (rev3_inv_register_record m s f p g b H Hl Hb Hid Hb' Hr) as H1.
  assert (Hlg : look f (put g s) = Some g) by (rewrite <- Hid; apply rev3_look_put_eq).
  apply (rev3_run_record fuel _ _ f g g H1 Hlg Hb' ltac:(congruence)); [|exact Hid|exact Hb'|exact Hr].
  apply (rev3_no_pend_record _ _ f g H1 Hlg). congruence.
Qed.

Lemma rev3_task_ok : forall m s t, Inv m s -> wp (mnext m (LTask t)) (c_run_task s t) Inv.
Proof.
  intros m s t H. pose proof (rev3_inv_task m s t H) as H1.
  set (m1 := mnext m (LTask t)) in *.
  unfold c_run_task, start_fiber. generalize task_fuel as fuel. intros fuel.
  (* A delivery's task closes the fiber's await, so the fiber has none open. *)
  assert (Hclosed : forall f tok g, look f s = Some g -> status g = Await tok ->
            (forall t', ends_await f t' (LTask t) = Nat.eqb t' tok) -> no_pend m1 f).
  { intros f tok g Hl Hs He t' Hin. apply rev3_pend_task in Hin. destruct Hin as [Hin Hn].
    destruct (i_pend _ _ H _ _ Hin) as [h [Hh Hs']]. rewrite Hl in Hh. injection Hh as <-.
    rewrite He in Hn. rewrite Hs in Hs'. injection Hs' as ->. rewrite Nat.eqb_refl in Hn.
    discriminate. }
  assert (Hrelease : forall f tok g e, look f s = Some g -> status g = Await tok ->
            (forall t', ends_await f t' (LTask t) = Nat.eqb t' tok) ->
            wp m1 (Emit (EvRelease f tok) (go fuel 0 s (unwind g e))) Inv).
  { intros f tok g e Hl Hs He. pose proof (Hclosed f tok g Hl Hs He) as Hn.
    assert (Hb : begun g = true) by (apply (rev3_begun_record m1 s f g H1 Hl); congruence).
    destruct (rev3_look_some _ _ _ Hl) as [Hid _].
    cbn [wp]. split.
    - apply rev3_mok_release.
      + exact (i_begun _ _ H1 _ _ Hl Hb).
      + intros Hin. destruct (i_ex _ _ H1 _ Hin) as [h [Hh Hf]]. rewrite Hl in Hh. congruence.
      + intros t' Hin. destruct (Hn t' Hin).
    - pose proof (rev3_inv_release m1 s f tok H1) as H2.
      destruct (rev3_unwind_fields g e) as [F1 [F2 F3]].
      apply (rev3_run_record fuel _ s f g _ H2 Hl Hb ltac:(congruence)); [|congruence..].
      intros t' Hin. apply rev3_pend_release in Hin. exact (Hn t' (proj1 Hin)). }
  destruct t as [|q|f tok o|f tok|f tok|f].
  - (* StartRoot *)
    destruct (look 0 s) as [r|] eqn:Hr; [exact H1|].
    set (g0 := new_fiber 0 (bodies (program s) (root_body (program s)))).
    change (begun g0) with false. change (fid g0) with 0. cbn [wp]. intros b.
    assert (H2 : Inv m1 (put g0 s)).
    { apply rev3_inv_put; [exact H1|exact (i_pos _ _ H1)|..]; cbn [g0 new_fiber fid begun status].
      - discriminate.
      - intros _. split; [|reflexivity]. intros Hin. exact (i_root _ _ H1 Hin Hr).
      - intros Hin. destruct (i_ex _ _ H1 _ Hin) as [h [Hh _]]. congruence.
      - intros tok Hin. destruct (i_pend _ _ H1 _ _ Hin) as [h [Hh _]]. congruence. }
    apply (rev3_start_record fuel m1 (put g0 s) 0 g0); [exact H2|exact (rev3_look_put_eq g0 s)|
      reflexivity..].
  - (* RunQueued *)
    destruct (look q s) as [g|] eqn:Hl; [|exact H1].
    destruct (rev3_look_some _ _ _ Hl) as [Hid _]. subst q.
    destruct (status g) eqn:Hs; try exact H1.
    destruct (queued g); [|exact H1].
    change (begun (set_queued g false)) with (begun g).
    destruct (begun g) eqn:Hb.
    + apply (rev3_run_record fuel m1 s (fid g) g); [exact H1|exact Hl|exact Hb|congruence| |
        reflexivity|exact Hb|exact Hs].
      apply (rev3_no_pend_record m1 s (fid g) g H1 Hl). congruence.
    + change (fid (set_queued g false)) with (fid g). cbn [wp]. intros b.
      apply (rev3_start_record fuel m1 s (fid g) g); [exact H1|exact Hl|exact Hb|reflexivity..|
        exact Hs].
  - (* Deliver *)
    destruct (look f s) as [g|] eqn:Hl; [|exact H1].
    destruct (status g) as [|tok'| | |] eqn:Hs; try exact H1.
    destruct (tok =? tok') eqn:Et; [|exact H1]. apply Nat.eqb_eq in Et. subst tok'.
    destruct (rev3_look_some _ _ _ Hl) as [Hid _].
    apply (rev3_run_record fuel m1 s f g); [exact H1|exact Hl| |congruence| |exact Hid| |
      reflexivity].
    + apply (rev3_begun_record m1 s f g H1 Hl). congruence.
    + apply (Hclosed f tok g Hl Hs). intros t'. simpl. rewrite Nat.eqb_refl. reflexivity.
    + apply (rev3_begun_record m1 s f g H1 Hl). congruence.
  - (* DeliverCancel *)
    destruct (look f s) as [g|] eqn:Hl; [|exact H1].
    destruct (status g) as [|tok'| | |] eqn:Hs; try exact H1.
    destruct (tok =? tok') eqn:Et; [|exact H1]. apply Nat.eqb_eq in Et. subst tok'.
    apply (Hrelease f tok g ExitInterrupted Hl Hs). intros t'. simpl. rewrite Nat.eqb_refl.
    reflexivity.
  - (* DeliverDefect *)
    destruct (look f s) as [g|] eqn:Hl; [|exact H1].
    destruct (status g) as [|tok'| | |] eqn:Hs; try exact H1.
    destruct (tok =? tok') eqn:Et; [|exact H1]. apply Nat.eqb_eq in Et. subst tok'.
    apply (Hrelease f tok g ExitDefect Hl Hs). intros t'. simpl. rewrite Nat.eqb_refl.
    reflexivity.
  - (* RequestInterrupt *)
    refine (rev3_wp_mono _ _ _ _ _ _ (proj2 (rev3_go_ok fuel) s f m1 H1)).
    intros m' s' [Hi _]. exact Hi.
Qed.

(** The concrete runtime meets the interface, for every task sequence. *)
Theorem rev3_meets_concrete : MeetsConcrete.
Proof.
  unfold MeetsConcrete, Meets. split.
  - apply rev3_i1_of_eq. intros s1 s2. simpl. tauto.
  - apply (rev3_meets_of_monitor concrete Inv).
    + exact rev3_inv_init.
    + exact rev3_task_ok.
Qed.

