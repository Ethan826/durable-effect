(** * Arrival: what one step does to the trace.

    [arrival_grow I cuts x y] is [arrival_ext] for a whole step: the cursor and the progress
    count may grow, and when [cuts] is true the step may also cut. A journal mismatch is only
    ever reported from an open attempt with something persisted. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Statements ArrivalBase ArrivalExt.
Import ListNotations.
Open Scope Z_scope.

Definition arrival_grow (I : Inputs) (cuts : bool) (x y : XState) : Prop :=
  (exists l, trace y = trace x ++ l /\
     (cuts = false -> forallb arrival_ok l = true) /\
     (existsb arrival_mm l = true -> phase x = POpen /\ persisted I <> [])) /\
  (prank (phase x) <= prank (phase y))%nat /\
  (cuts = false -> some_cut (phase y) = true -> phase y = phase x) /\
  (arrival_nc x -> arrival_nc y) /\
  (cursor x <= cursor y)%nat /\ (progress x <= progress y)%nat.

Lemma arrival_grow_refl : forall I c x, arrival_grow I c x x.
Proof.
  intros. split.
  - exists []. rewrite app_nil_r. split; [reflexivity|split; [reflexivity|discriminate]].
  - split; [lia|]. split; [auto|]. split; [tauto|]. split; lia.
Qed.

Lemma arrival_grow_trans : forall I c x y z,
  arrival_grow I c x y -> arrival_grow I c y z -> arrival_grow I c x z.
Proof.
  intros I c x y z ((l1&E1&O1&M1)&P1&C1&N1&U1&G1) ((l2&E2&O2&M2)&P2&C2&N2&U2&G2).
  split; [|split; [lia|split; [|split; [tauto|split; lia]]]].
  - exists (l1 ++ l2). rewrite E2, E1, app_assoc. split; [reflexivity|].
    split; [intros Hc; rewrite forallb_app, (O1 Hc), (O2 Hc); reflexivity|].
    rewrite existsb_app. intros H. apply orb_true_iff in H. destruct H as [H|H]; auto.
    destruct (M2 H) as [Hp Hn]. split; [|exact Hn].
    rewrite Hp in P1. destruct (phase x); cbn in P1; [reflexivity|lia|lia].
  - intros Hc H. specialize (C2 Hc H). rewrite C2 in H |- *. auto.
Qed.

Lemma arrival_grow_cuts : forall I x y, arrival_grow I false x y -> arrival_grow I true x y.
Proof.
  intros I x y ((l&E&O&M)&P&C&H). split; [|split; [exact P|split; [discriminate|exact H]]].
  exists l. split; [exact E|]. split; [discriminate|exact M].
Qed.

Lemma arrival_ext_grow : forall I b c x y, arrival_ext I b x y ->
  (b = true -> phase x = POpen) -> arrival_grow I c x y.
Proof.
  intros I b c x y ((l&E&O&M)&P&C&N&U&G) Hb.
  split; [|split; [exact P|split; [intros _; exact C|split; [exact N|lia]]]].
  exists l. split; [exact E|]. split; [intros _; exact O|].
  intros H. destruct (M H) as [B Hn]. auto.
Qed.

(** A field update that only moves the counters forwards. *)
Lemma arrival_grow_leaf : forall I c x y,
  trace y = trace x -> phase y = phase x -> next_cmd y = next_cmd x ->
  (cursor x <= cursor y)%nat -> (progress x <= progress y)%nat -> arrival_grow I c x y.
Proof.
  intros I c x y E P N U G. split.
  - exists []. rewrite E, app_nil_r. split; [reflexivity|split; [reflexivity|discriminate]].
  - rewrite P. split; [lia|]. split; [auto|]. unfold arrival_nc. rewrite E, N.
    split; [tauto|split; assumption].
Qed.

Lemma arrival_grow_micro : forall I c x m, arrival_grow I c x (set_micro x m).
Proof. intros. apply arrival_grow_leaf; reflexivity. Qed.

(** ** The boundary *)

Lemma arrival_ext_progress : forall I b x y, arrival_ext I b x y -> progress y = progress x.
Proof. intros I b x y (_&_&_&_&_&G). exact G. Qed.

Lemma arrival_at_boundary_sub_grow : forall I Sch x sb y,
  phase x = POpen -> at_boundary_sub I Sch x sb = Some y ->
  arrival_grow I false x y /\ progress y = progress x.
Proof.
  intros I Sch x sb y Hp H. unfold at_boundary_sub in H.
  assert (Hc : arrival_grow I false x (set_cursor x (S (cursor x))))
    by (apply arrival_grow_leaf; cbn; try reflexivity; lia).
  destruct (arrived Sch (micro x) <=? cursor x)%nat; [discriminate|].
  destruct (nth_error (entries I) (cursor x)) as [[c r|]|]; [| |discriminate].
  - destruct (Nat.eqb c (sub_cmd sb)).
    + injection H as <-. split; [|transitivity (progress (set_cursor x (S (cursor x))));
      [eapply arrival_ext_progress; apply arrival_on_notify_ext|reflexivity]].
      eapply arrival_grow_trans; [exact Hc|].
      eapply arrival_ext_grow; [apply arrival_on_notify_ext|]. intros _. exact Hp.
    + destruct (c <? next_cmd x)%nat; [|discriminate]. injection H as <-.
      split; [exact Hc|reflexivity].
  - injection H as <-. split; [|transitivity (progress (set_cursor x (S (cursor x))));
      [eapply arrival_ext_progress; apply arrival_on_cancel_ext|reflexivity]].
    eapply arrival_grow_trans; [exact Hc|].
    eapply arrival_ext_grow; [apply arrival_on_cancel_ext|]. intros _. exact Hp.
Qed.

Lemma arrival_at_boundary_grow : forall I Sch x y,
  at_boundary I Sch x = Some y -> arrival_grow I false x y /\ progress y = progress x.
Proof.
  intros I Sch x y H. unfold at_boundary in H.
  destruct (phase x) eqn:Hp; [| |discriminate].
  - destruct (held x) eqn:Hh, (waiter x) as [[[f tok] op]|] eqn:Hw.
    + injection H as <-. split; [|reflexivity].
      destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf].
      apply arrival_grow_leaf; cbn; reflexivity.
    + destruct (sub x) as [sb|]; [eapply arrival_at_boundary_sub_grow; eassumption|].
      injection H as <-. split; [|apply (arrival_ext_progress I false); apply arrival_violate_ext].
      eapply arrival_ext_grow; [apply arrival_violate_ext|]. discriminate.
    + destruct (sub x) as [sb|]; [eapply arrival_at_boundary_sub_grow; eassumption|].
      injection H as <-.
      split; [|transitivity (progress (set_waiter x None));
        [eapply arrival_ext_progress; apply arrival_issue_op_ext|reflexivity]].
      apply (arrival_grow_trans _ _ _ (set_waiter x None));
        [apply arrival_grow_leaf; cbn; reflexivity|].
      eapply arrival_ext_grow; [apply arrival_issue_op_ext|]. intros _. exact Hp.
    + destruct (sub x) as [sb|]; [eapply arrival_at_boundary_sub_grow; eassumption|].
      injection H as <-. split; [|apply (arrival_ext_progress I false); apply arrival_violate_ext].
      eapply arrival_ext_grow; [apply arrival_violate_ext|]. discriminate.
  - injection H as <-.
    split; [|apply (arrival_ext_progress I false); apply arrival_finish_verdict_ext].
    eapply arrival_ext_grow; [apply arrival_finish_verdict_ext|]. discriminate.
Qed.

(** ** A task *)

(** What [run_head] does before it runs the task's script. *)
Definition arrival_pre (x : XState) (t : Task) : XState :=
  let x1 := match task_action t with Some a => emit x a | None => x end in
  match t, awaiter x1 with
  | Deliver f tok _, Some a | DeliverCancel f tok, Some a =>
      if pair_eqb a (f, tok) then set_awaiter x1 None else x1
  | _, _ => x1
  end.

Lemma arrival_run_head_unfold : forall R I x r t rest,
  run_head R I x r t rest =
  interp I (arrival_pre (set_progress (set_queue x rest) (S (progress x))) t)
    (run_task R r t).
Proof. reflexivity. Qed.

Lemma arrival_pre_ext : forall I x t,
  arrival_ext I false x (arrival_pre x t) /\ phase (arrival_pre x t) = phase x.
Proof.
  intros. destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf].
  unfold arrival_pre. destruct t; arrival_norm; cbn [task_action];
    arrival_split_eqn; split; arrival_split_eqn; reflexivity.
Qed.

Lemma arrival_run_head_grow : forall R I x r t rest,
  arrival_grow I false x (fst (run_head R I x r t rest)).
Proof.
  intros. rewrite arrival_run_head_unfold.
  set (x0 := set_progress (set_queue x rest) (S (progress x))).
  assert (H0 : arrival_grow I false x x0)
    by (apply arrival_grow_leaf; cbn; try reflexivity; lia).
  destruct (arrival_pre_ext I x0 t) as [H1 P1].
  destruct (arrival_interp_ext I (run_task R r t) (arrival_pre x0 t)) as [H2 H3].
  eapply arrival_grow_trans; [exact H0|].
  eapply arrival_grow_trans; [eapply arrival_ext_grow; [exact H1|discriminate]|].
  destruct (phase (arrival_pre x0 t)) eqn:Hp.
  - eapply arrival_ext_grow; [exact H2|]. intros _. exact Hp.
  - eapply arrival_ext_grow; [apply H3; congruence|discriminate].
  - eapply arrival_ext_grow; [apply H3; congruence|discriminate].
Qed.

Lemma arrival_no_command : forall l, commands l = [] ->
  forall c k o, ~ In (ACommand c k o) l.
Proof.
  induction l as [|a l IH]; intros C c k o Hin; [exact Hin|].
  destruct Hin as [E|Hin]; [subst a; discriminate|].
  destruct a; cbn in C; try discriminate; eapply IH; eassumption.
Qed.

Lemma arrival_nc_noncmd : forall x y l, trace y = trace x ++ l -> commands l = [] ->
  next_cmd y = next_cmd x -> arrival_nc x -> arrival_nc y.
Proof.
  intros x y l E C N [N1 N2]. unfold arrival_nc. rewrite E, N, arrival_commands_app, C,
    app_nil_r. split; [|exact N2]. apply arrival_numbered_app. split; [exact N1|].
  apply arrival_numbered_one; [|rewrite C; cbn; lia].
  intros c k o Hin. exfalso. eapply arrival_no_command; eassumption.
Qed.

Lemma arrival_on_cut_fields : forall x k,
  trace (on_cut x k) = trace x ++ [ACut k] /\ next_cmd (on_cut x k) = next_cmd x /\
  cursor (on_cut x k) = cursor x /\ progress (on_cut x k) = progress x /\
  (prank (phase x) <= prank (phase (on_cut x k)))%nat.
Proof.
  intros. destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf].
  unfold on_cut, close. destruct k, xp; try destruct cut; arrival_norm; cbn [prank];
    repeat split; lia.
Qed.

Lemma arrival_on_cut_grow : forall I x k, arrival_grow I true x (on_cut x k).
Proof.
  intros. destruct (arrival_on_cut_fields x k) as (E&N&U&G&P).
  split; [|split; [exact P|split; [discriminate|split; [|lia]]]].
  - exists [ACut k]. split; [exact E|]. split; [discriminate|]. cbn. discriminate.
  - apply arrival_nc_noncmd with (l := [ACut k]); auto.
Qed.

(** One step, under any schedule; and under a schedule with no cut and no stop, a step
    that adds no cut. *)
Lemma arrival_step_grow : forall R I Sch s,
  arrival_grow I true (xs s) (xs (step R I Sch s)) /\
  (cut_at Sch = None -> stop_at Sch = None ->
   arrival_grow I false (xs s) (xs (step R I Sch s))).
Proof.
  intros R I Sch [x r]. unfold step. cbn [xs rs].
  destruct (phase x) eqn:Hp;
    [| |split; intros; apply arrival_grow_refl].
  all: destruct (stop_due Sch x) eqn:Hs.
  all: try (split; [|intros _ Hn; unfold stop_due in Hs; rewrite Hn in Hs; discriminate];
            cbn [xs]; eapply arrival_grow_trans; [|apply arrival_grow_micro];
            split; [exists []; rewrite app_nil_r; split; [reflexivity|]; split;
                    [discriminate|cbn; discriminate]|];
            cbn; rewrite Hp; split; [cbn; lia|]; split; [discriminate|];
            split; [tauto|split; lia]).
  all: destruct (foreign_due I x) as [fi|].
  all: try (cbn [xs];
            assert (H : arrival_grow I false x
                          (set_micro (on_foreign (set_fseen x (Some (progress x))) fi)
                             (S (micro x))));
            [eapply arrival_grow_trans; [|apply arrival_grow_micro];
             apply (arrival_grow_trans _ _ _ (set_fseen x (Some (progress x))));
             [apply arrival_grow_leaf; cbn; reflexivity|];
             eapply arrival_ext_grow; [apply arrival_on_foreign_ext|discriminate]
            |split; [apply arrival_grow_cuts|intros _ _]; exact H]).
  all: destruct (cut_due Sch x) as [k|] eqn:Hc.
  all: try (split; [|intros Hn _; unfold cut_due in Hc; rewrite Hn in Hc; discriminate];
            cbn [xs]; eapply arrival_grow_trans; [apply arrival_on_cut_grow|];
            apply arrival_grow_micro).
  all: destruct (queue x) as [|t rest].
  all: try (destruct (run_head R I x r t rest) as [x' r'] eqn:Hr; cbn [xs];
            assert (H : arrival_grow I false x (set_micro x' (S (micro x))));
            [eapply arrival_grow_trans; [|apply arrival_grow_micro];
             pose proof (arrival_run_head_grow R I x r t rest) as G; rewrite Hr in G;
             exact G
            |split; [apply arrival_grow_cuts|intros _ _]; exact H]).
  all: destruct (at_boundary I Sch x) as [y|] eqn:Hb; cbn [xs].
  all: try (assert (H : arrival_grow I false x (set_micro x (S (micro x))))
              by apply arrival_grow_micro;
            split; [apply arrival_grow_cuts|intros _ _]; exact H).
  all: destruct (arrival_at_boundary_grow I Sch x y Hb) as [G E].
  all: assert (H : arrival_grow I false x
                     (set_micro (set_progress y (S (progress x))) (S (micro x))));
    [eapply arrival_grow_trans; [exact G|];
     eapply arrival_grow_trans; [|apply arrival_grow_micro];
     apply arrival_grow_leaf; cbn; try reflexivity; lia
    |split; [apply arrival_grow_cuts|intros _ _]; exact H].
Qed.
