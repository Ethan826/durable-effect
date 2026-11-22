(** * Lemmas for S8_upper: the frame of a fiber's run, and the bound as a tracked property.

    S8_upper needs two facts that the generic tool of SingleStepLemmas.v does not track. The
    sample index changes only at a delivery. And the awaited fiber is in the fiber table, so
    a delivery always resumes it: if [resume] found no fiber, the awaited sleep would stay
    awaited and be delivered again, adding its chunk to [L] a second time with no new sleep
    command to pay for the lead. *)

From Coq Require Import List ZArith Bool Arith Lia.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model Executor Statements SingleStepLemmas
  SingleStepInvariants.
Import ListNotations.
Open Scope Z_scope.

(** ** The frame: what a fiber's run leaves alone *)

(** The handles in the fiber table. *)
Definition hs (st : State) : list nat := map handle (fibers st).

(** The awaited fiber is in the fiber table. *)
Definition J (st : State) : Prop :=
  forall aw, awaited st = Some aw -> In (awaited_handle aw) (hs st).

(** From [st] to [r]: [J] is kept, the sample index is unchanged, no handle is lost. *)
Definition Frame (st r : State) : Prop :=
  (J st -> J r) /\ next_sample r = next_sample st /\ incl (hs st) (hs r).

Lemma frame_trans : forall a b c, Frame a b -> Frame b c -> Frame a c.
Proof.
  intros a b c (H1 & H2 & H3) (H4 & H5 & H6). split; [auto|]. split.
  - congruence.
  - intros x Hx. auto.
Qed.

Lemma frame_same : forall st r,
  awaited r = awaited st -> hs r = hs st -> next_sample r = next_sample st -> Frame st r.
Proof.
  intros st r Ha Hh Hn. split; [|split; [exact Hn|]].
  - intros HJ aw Haw. rewrite Hh. apply HJ. congruence.
  - rewrite Hh. intros x Hx. exact Hx.
Qed.

Lemma hs_put : forall f fs, map handle (put_fiber f fs) = map handle fs.
Proof.
  intros f fs. unfold put_fiber. rewrite map_map. apply map_ext. intros g.
  destruct (Nat.eqb (handle g) (handle f)) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E. symmetry. exact E.
Qed.

Lemma find_fiber_in : forall h fs g,
  find_fiber h fs = Some g -> In (handle g) (map handle fs) /\ handle g = h.
Proof.
  intros h fs g Hf. unfold find_fiber in Hf.
  pose proof (find_some _ _ Hf) as [Hin Heq]. apply Nat.eqb_eq in Heq.
  split; [apply in_map; exact Hin | exact Heq].
Qed.

Lemma find_fiber_none : forall h fs, In h (map handle fs) -> find_fiber h fs <> None.
Proof.
  intros h fs Hin Hf. apply in_map_iff in Hin. destruct Hin as (g & Hg & Hin).
  unfold find_fiber in Hf. pose proof (find_none _ _ Hf g Hin) as Hb. cbn in Hb.
  rewrite Hg, Nat.eqb_refl in Hb. discriminate.
Qed.

(** The awaited operation is unchanged or cleared, and the table keeps its handles. *)
Lemma frame_clear : forall st r,
  (awaited r = awaited st \/ awaited r = None) -> hs r = hs st ->
  next_sample r = next_sample st -> Frame st r.
Proof.
  intros st r Ha Hh Hn. split; [|split; [exact Hn|]].
  - intros HJ aw Haw. rewrite Hh. apply HJ.
    destruct Ha as [Ha|Ha]; rewrite Ha in Haw; [exact Haw | discriminate].
  - rewrite Hh. intros x Hx. exact Hx.
Qed.

Lemma interrupt_frame : forall st h, Frame st (interrupt_fiber st h).
Proof.
  intros st h. unfold interrupt_fiber.
  destruct (find_fiber h (fibers st)) as [f|];
    [|apply frame_same; reflexivity].
  destruct (status f);
    try (apply frame_same; reflexivity);
    destruct (awaited st) as [[h' op|h' op c r]|] eqn:Ha;
    try destruct (Nat.eqb h' h);
    (apply frame_clear;
     [ cbn -[put_fiber]; rewrite ?Ha; auto
     | unfold hs; cbn -[put_fiber]; apply hs_put
     | reflexivity ]).
Qed.

Lemma fold_interrupt_frame : forall fs st,
  Frame st (fold_left (fun s f => interrupt_fiber s (handle f)) fs st).
Proof.
  induction fs as [|f fs IH]; intros st; [apply frame_same; reflexivity|].
  cbn. eapply frame_trans; [apply interrupt_frame | apply IH].
Qed.

Lemma end_attempt_frame : forall st how, Frame st (end_attempt st how).
Proof.
  intros st []; unfold end_attempt.
  - eapply frame_trans; [apply fold_interrupt_frame | apply frame_same; reflexivity].
  - apply frame_same; reflexivity.
Qed.

(** A state that keeps the awaited operation and the sample index and puts one fiber back. *)
Ltac frame_put :=
  apply frame_same; unfold hs; cbn [awaited fibers next_sample update emit with_fibers];
  rewrite ?hs_put; reflexivity.

(** A new awaited operation for fiber [h], which is in the table. *)
Lemma frame_await : forall st r aw,
  In (awaited_handle aw) (hs st) -> awaited r = Some aw -> hs r = hs st ->
  next_sample r = next_sample st -> Frame st r.
Proof.
  intros st r aw Hin Ha Hh Hn. split; [|split; [exact Hn|]].
  - intros _ b Hb. rewrite Ha in Hb. injection Hb as <-. rewrite Hh. exact Hin.
  - rewrite Hh. intros x Hx. exact Hx.
Qed.

Lemma run_fiber_frame : forall pol P E fuel ops st f,
  In (handle f) (hs st) -> Frame st (run_fiber pol P E fuel ops st f).
Proof.
  intros pol P E. induction fuel as [|fuel IH]; intros ops st f Hin;
    [cbn [run_fiber]; frame_put|].
  cbn -[update emit with_fibers put_fiber set_code find_fiber new_fiber
        interrupt_fiber violate max_ops].
  destruct (finished st); [apply frame_same; reflexivity|].
  destruct ops as [|ops]; [frame_put|].
  destruct (observe (code f)) as [r|t|X e k]; [frame_put | apply IH; exact Hin|].
  destruct e;
    cbn -[update emit with_fibers put_fiber set_code find_fiber new_fiber
          interrupt_fiber violate max_ops].
  - eapply frame_trans; [|apply IH; exact Hin]. frame_put.
  - eapply frame_trans; [|apply IH; exact Hin]. frame_put.
  - assert (Hst : Frame st (update st (put_fiber (set_code f (k (next_handle st)) NoPending
      Ready) (fibers st) ++ [new_fiber (next_handle st) (bodies P n)]) (queue st)
      (awaited st) (abandoned st) (next_op st) (next_sample st) (S (next_handle st))
      (draws st) (logical st) (trace st) (finished st))).
    { split; [|split; [reflexivity|]].
      - intros HJ aw Haw. unfold hs. cbn. rewrite map_app, hs_put. apply in_or_app.
        left. apply HJ. exact Haw.
      - intros x Hx. unfold hs. cbn. rewrite map_app, hs_put. apply in_or_app.
        left. exact Hx. }
    destruct f0.
    + eapply frame_trans; [exact Hst|]. eapply frame_trans; [|apply IH].
      * apply frame_same; reflexivity.
      * unfold hs. cbn. rewrite map_app, hs_put. apply in_or_app. left. exact Hin.
    + eapply frame_trans; [exact Hst|].
      match goal with |- context [run_fiber pol P E fuel max_ops ?A ?c] =>
        assert (Hc := IH max_ops A c);
        remember (run_fiber pol P E fuel max_ops A c) as s2 eqn:E2; clear E2 end.
      assert (Hc' := Hc ltac:(unfold hs; cbn; rewrite map_app, hs_put; apply in_or_app;
        right; left; reflexivity)).
      destruct (find_fiber (handle f) (fibers s2)) as [g|] eqn:Hg; [|exact Hc'].
      eapply frame_trans; [exact Hc'|]. apply IH.
      exact (proj1 (find_fiber_in _ _ _ Hg)).
  - destruct (awaited st) eqn:Ha;
      [apply frame_same; reflexivity|].
    apply frame_await with (AwaitOp (handle f) (next_op st)); [exact Hin | reflexivity | |
      reflexivity].
    unfold hs. cbn -[put_fiber]. apply hs_put.
  - destruct (chunk_long_sleeps pol), d as [ms|];
      try destruct (ms <=? 0)%Z; try destruct (ms <=? max_chunk)%Z;
      try destruct (ms <=? max_safe)%Z;
      try frame_put;
      (destruct (awaited st) eqn:Ha; [apply frame_same; reflexivity|]);
      (eapply frame_await; [| reflexivity | | reflexivity];
        [exact Hin | unfold hs; cbn -[put_fiber]; apply hs_put]).
  - frame_put.
  - match goal with |- context [interrupt_fiber ?A n] =>
      assert (Hi := interrupt_frame A n);
      remember (interrupt_fiber A n) as s2 eqn:E2; clear E2 end.
    assert (Hp : Frame st (with_fibers st
      (put_fiber (set_code f (k tt) NoPending Ready) (fibers st)))) by frame_put.
    destruct (find_fiber (handle f) (fibers s2)) as [g|] eqn:Hg;
      [|eapply frame_trans; [exact Hp | exact Hi]].
    eapply frame_trans; [exact Hp|]. eapply frame_trans; [exact Hi|]. apply IH.
    exact (proj1 (find_fiber_in _ _ _ Hg)).
  - frame_put.
  - apply IH. exact Hin.
  - eapply frame_trans; [|apply IH; exact Hin]. apply frame_same; reflexivity.
Qed.

(** ** The bound as a property of the tracked fields *)

Definition is_sleep (a : Action) : bool :=
  match a with SleepCommand _ _ _ => true | _ => false end.

Lemma sleeps_snoc : forall tr a,
  sleep_commands (tr ++ [a]) = (sleep_commands tr + if is_sleep a then 1 else 0)%nat.
Proof.
  intros tr a. unfold sleep_commands. rewrite filter_app, length_app.
  destruct a; reflexivity.
Qed.

(** What an awaited sleep keeps back from the bound: the lead its completion may use. *)
Definition reserve (lead : Z) (aw : option Awaited) : Z :=
  match aw with Some (AwaitSleep _ _ _ _) => lead | _ => 0 end.

(** [L], with the awaited sleep's lead kept back, is within [T] plus a lead per sleep
    command; and an awaited sleep's command is among them. *)
Definition U (lead T : Z) : Inv := fun tr aw _ l =>
  l + reserve lead aw <= T + Z.of_nat (sleep_commands tr) * lead /\
  (forall h op c r, aw = Some (AwaitSleep h op c r) -> (1 <= sleep_commands tr)%nat).

Lemma lead_products : forall lead n, 0 <= lead ->
  0 <= Z.of_nat n * lead /\ ((1 <= n)%nat -> lead <= Z.of_nat n * lead) /\
  Z.of_nat (n + 1) * lead = Z.of_nat n * lead + lead.
Proof.
  intros lead n Hl. split; [|split].
  - apply Z.mul_nonneg_nonneg; lia.
  - intros Hn. rewrite <- (Z.mul_1_l lead) at 1. apply Z.mul_le_mono_nonneg_r; lia.
  - rewrite Nat2Z.inj_add. ring.
Qed.

Lemma reserve_range : forall lead aw, 0 <= lead ->
  reserve lead aw = 0 \/ reserve lead aw = lead.
Proof. intros lead [[]|] Hl; cbn; auto. Qed.

Lemma U_closed : forall lead T, 0 <= lead -> closed policy_v1 (U lead T).
Proof.
  intros lead T Hl. split; unfold U.
  - intros tr aw n l a [Hc _] [H1 H2]. rewrite sleeps_snoc.
    replace (is_sleep a) with false by (destruct a; try discriminate Hc; reflexivity).
    rewrite Nat.add_0_r. split; assumption.
  - intros tr aw n l h [H1 H2]. rewrite sleeps_snoc. cbn [is_sleep].
    rewrite Nat.add_0_r. split.
    + pose proof (reserve_range lead aw Hl).
      destruct aw as [[h' op|h' op c r]|]; cbn [cleared awaited_handle];
        try destruct (Nat.eqb h' h); cbn [reserve] in *; lia.
    + intros h' op c r Hs. apply (H2 h' op c r). exact (cleared_some _ _ _ Hs).
  - intros tr n l h k a [H1 H2]. rewrite sleeps_snoc. cbn [is_sleep reserve] in *.
    rewrite Nat.add_0_r. split; [exact H1 | discriminate].
  - intros tr n l h c r _ [H1 _]. rewrite sleeps_snoc. cbn [is_sleep reserve] in *.
    destruct (lead_products lead (sleep_commands tr) Hl) as (_ & _ & Hp).
    split; [rewrite Hp; lia | intros; lia].
Qed.
