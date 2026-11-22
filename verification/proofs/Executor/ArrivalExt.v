(** * Arrival: what each of the executor's functions does to the trace.

    [arrival_ext I b x y] says that [y] extends [x]'s trace without a cut, can report a
    journal mismatch only if [b] is true and something is persisted, never moves the phase
    backwards or into a closing after a cut, keeps the commands numbered in order, and leaves
    the cursor and the progress count alone. Every function below the step has this
    relation from its argument to its result. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Statements ArrivalBase.
Import ListNotations.
Open Scope Z_scope.

Definition arrival_ok (a : Action) : bool := match a with ACut _ => false | _ => true end.
Definition arrival_mm (a : Action) : bool :=
  match a with AExit VMismatch => true | _ => false end.

Definition prank (p : Phase) : nat :=
  match p with POpen => 0 | PClosing _ => 1 | PDone => 2 end.
Definition some_cut (p : Phase) : bool :=
  match p with PClosing (Some _) => true | _ => false end.

(** The commands of a trace are numbered from [n] in the order they were issued. *)
Fixpoint arrival_numbered (n : nat) (t : list Action) : Prop :=
  match t with
  | [] => True
  | ACommand c _ _ :: r => c = n /\ arrival_numbered (S n) r
  | _ :: r => arrival_numbered n r
  end.

Definition arrival_nc (x : XState) : Prop :=
  arrival_numbered 0 (trace x) /\ next_cmd x = length (commands (trace x)).

Definition arrival_ext (I : Inputs) (b : bool) (x y : XState) : Prop :=
  (exists l, trace y = trace x ++ l /\ forallb arrival_ok l = true /\
     (existsb arrival_mm l = true -> b = true /\ persisted I <> [])) /\
  (prank (phase x) <= prank (phase y))%nat /\
  (some_cut (phase y) = true -> phase y = phase x) /\
  (arrival_nc x -> arrival_nc y) /\
  cursor y = cursor x /\ progress y = progress x.

(** ** Numbering *)

Lemma arrival_commands_app : forall t l, commands (t ++ l) = commands t ++ commands l.
Proof. intros. unfold commands. apply flat_map_app. Qed.

Lemma arrival_numbered_app : forall t n l,
  arrival_numbered n (t ++ l) <->
  arrival_numbered n t /\ arrival_numbered (n + length (commands t)) l.
Proof.
  induction t as [|a t IH]; intros n l; cbn.
  - rewrite Nat.add_0_r. tauto.
  - destruct a; cbn; change (flat_map _ t) with (commands t); try apply IH.
    rewrite IH. replace (n + S (length (commands t)))%nat
      with (S n + length (commands t))%nat by lia. tauto.
Qed.

Lemma arrival_numbered_one : forall l m,
  (forall c k o, In (ACommand c k o) l -> c = m) -> (length (commands l) <= 1)%nat ->
  arrival_numbered m l.
Proof.
  induction l as [|a l IH]; intros m Hc Hl; cbn; [exact I|].
  destruct a; cbn in Hl; change (flat_map _ l) with (commands l) in Hl; try (apply IH; [intros; eapply Hc; right; eassumption|exact Hl]).
  split; [eapply Hc; left; reflexivity|].
  assert (E : commands l = []) by (destruct (commands l); [reflexivity|cbn in Hl; lia]).
  clear Hl Hc IH. revert m.
  induction l as [|a l IH]; intros m; cbn; [exact I|].
  destruct a; cbn in E; try discriminate; apply IH; exact E.
Qed.

(** ** The relation *)

Lemma arrival_ext_refl : forall I b x, arrival_ext I b x x.
Proof.
  intros. split.
  - exists []. rewrite app_nil_r. split; [reflexivity|split; [reflexivity|discriminate]].
  - split; [lia|]. split; [auto|]. split; [tauto|]. split; reflexivity.
Qed.

Lemma arrival_ext_trans : forall I b x y z,
  arrival_ext I b x y -> arrival_ext I b y z -> arrival_ext I b x z.
Proof.
  intros I b x y z ((l1&E1&O1&M1)&P1&C1&N1&U1&G1) ((l2&E2&O2&M2)&P2&C2&N2&U2&G2).
  split; [|split; [lia|split; [|split; [tauto|split; congruence]]]].
  - exists (l1 ++ l2). rewrite E2, E1, app_assoc. split; [reflexivity|].
    rewrite forallb_app, O1, O2. split; [reflexivity|].
    rewrite existsb_app. intros H. apply orb_true_iff in H. destruct H; auto.
  - intros H. specialize (C2 H). rewrite C2 in H |- *. auto.
Qed.

Lemma arrival_ext_weaken : forall I b x y, arrival_ext I false x y -> arrival_ext I b x y.
Proof.
  intros I b x y ((l&E&O&M)&H). split; [|exact H].
  exists l. split; [exact E|]. split; [exact O|].
  intros Hm. destruct (M Hm). discriminate.
Qed.

(** The lemma every leaf of a fully unfolded function is closed with. *)
Lemma arrival_ext_leaf : forall I b x y l,
  trace y = trace x ++ l ->
  forallb arrival_ok l = true ->
  (existsb arrival_mm l = true -> b = true /\ persisted I <> []) ->
  (prank (phase x) <= prank (phase y))%nat ->
  (some_cut (phase y) = true -> phase y = phase x) ->
  (forall c k o, In (ACommand c k o) l -> c = next_cmd x) ->
  next_cmd y = (next_cmd x + length (commands l))%nat ->
  (length (commands l) <= 1)%nat ->
  cursor y = cursor x -> progress y = progress x ->
  arrival_ext I b x y.
Proof.
  intros I b x y l E O M P C Nc Nn Nl U G.
  split; [exists l; auto|]. do 2 (split; [assumption|]).
  split; [|split; assumption]. intros H. split.
  - rewrite E. apply arrival_numbered_app. destruct H as [H1 H2]. split; [exact H1|].
    rewrite <- H2. apply arrival_numbered_one; [|exact Nl]. cbn. exact Nc.
  - rewrite Nn, E, arrival_commands_app, length_app. destruct H as [_ ->]. reflexivity.
Qed.

Lemma arrival_persisted_some : forall I c k, nth_error (persisted I) c = Some k ->
  persisted I <> [].
Proof. intros I c k H E. rewrite E in H. destruct c; discriminate. Qed.

Ltac arrival_leaf :=
  eapply arrival_ext_leaf;
  [ cbn [trace]; rewrite <- ?app_assoc;
    first [reflexivity | instantiate (1 := []); symmetry; apply app_nil_r]
  | reflexivity
  | cbn; first [ discriminate
               | intros _; split; [reflexivity|]; eapply arrival_persisted_some;
                 eassumption ]
  | cbn; repeat match goal with |- context [prank ?p] => is_var p; destruct p end;
    cbn; lia
  | cbn; first [intros; reflexivity | discriminate]
  | cbn; intros ? ? ? Hin; repeat (destruct Hin as [Hin|Hin]; [congruence|]);
    contradiction
  | cbn; lia
  | cbn; lia
  | reflexivity
  | reflexivity ].

Ltac arrival_split_eqn :=
  repeat (try (solve [arrival_leaf]);
          match goal with
          | |- context [match ?e with _ => _ end] =>
              lazymatch e with
              | context [match _ with _ => _ end] => fail
              | _ => let E := fresh "E" in destruct e eqn:E
              end
          end; arrival_norm).

(** ** The functions below the step *)

Ltac arrival_ext_by := arrival_norm; arrival_split_eqn.

Lemma arrival_issue_ext : forall I x k o s, arrival_ext I true x (issue I x k o s).
Proof. intros. destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf]. unfold issue, finish. arrival_ext_by. Qed.

Lemma arrival_violate_ext : forall I x v, arrival_ext I false x (violate x v).
Proof. intros. destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf]. unfold violate, close. arrival_ext_by. Qed.

Lemma arrival_on_start_ext : forall I x f tok op,
  arrival_ext I true x (on_start I x f tok op) /\
  (phase x <> POpen -> arrival_ext I false x (on_start I x f tok op)).
Proof.
  intros. destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf].
  unfold on_start, slot_held, violate, close, issue_op, issue, finish.
  cbn [phase]. destruct xp; [split; [|intros H; congruence]|split; [|intros _]..];
    arrival_ext_by.
Qed.

Lemma arrival_on_event_ext : forall I x e,
  arrival_ext I true x (on_event I x e) /\
  (phase x <> POpen -> arrival_ext I false x (on_event I x e)).
Proof.
  intros. destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf].
  unfold on_event, on_start, slot_held, violate, close, issue_op, issue, finish, on_release.
  cbn [phase]. destruct xp; [split; [|intros H; congruence]|split; [|intros _]..];
    arrival_ext_by.
Qed.

Lemma arrival_interp_ext : forall {X} I (s : Script X) x,
  arrival_ext I true x (fst (interp I x s)) /\
  (phase x <> POpen -> arrival_ext I false x (fst (interp I x s))).
Proof.
  intros X I s. induction s as [r|e k IH|f k IH|f k IH|f k IH]; intros x; cbn [interp fst].
  - split; intros; apply arrival_ext_refl.
  - destruct (arrival_on_event_ext I x e) as [H1 H2].
    destruct (IH (on_event I x e)) as [H3 H4]. split.
    + eapply arrival_ext_trans; eassumption.
    + intros Hp. specialize (H2 Hp). eapply arrival_ext_trans; [exact H2|]. apply H4.
      destruct H2 as (_&P&_). intros E. rewrite E in P. revert Hp P.
      destruct (phase x); cbn; intros; congruence || lia.
  - assert (H : forall b, arrival_ext I b x
      match phase x with PDone => x | _ => emit x (AClock f (logical x)) end).
    { intros b. destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf].
      arrival_ext_by. }
    destruct (IH (logical x) (match phase x with PDone => x
                              | _ => emit x (AClock f (logical x)) end)) as [H3 H4].
    split; [eapply arrival_ext_trans; [apply H|exact H3]|].
    intros Hp. eapply arrival_ext_trans; [apply H|]. apply H4. revert Hp.
    destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf].
    destruct xp; cbn; congruence.
  - assert (H : forall b, arrival_ext I b x
      match phase x with PDone => x
      | _ => emit (set_draws x (S (draws x))) (ADraw f (stream I (draws x))) end).
    { intros b. destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf].
      arrival_ext_by. }
    destruct (IH (stream I (draws x)) (match phase x with PDone => x
      | _ => emit (set_draws x (S (draws x))) (ADraw f (stream I (draws x))) end))
      as [H3 H4].
    split; [eapply arrival_ext_trans; [apply H|exact H3]|].
    intros Hp. eapply arrival_ext_trans; [apply H|]. apply H4. revert Hp.
    destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf].
    destruct xp; cbn; congruence.
  - set (x1 := match phase x with PDone => x | _ => emit x (ARegister f) end).
    assert (H : forall b, arrival_ext I b x (set_live x1 (live x1 ++ [f]))).
    { intros b. subst x1.
      destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf].
      arrival_ext_by. }
    destruct (IH (match phase x with PClosing _ => true | _ => false end)
                 (set_live x1 (live x1 ++ [f]))) as [H3 H4].
    split; [eapply arrival_ext_trans; [apply H|exact H3]|].
    intros Hp. eapply arrival_ext_trans; [apply H|]. apply H4. revert Hp. subst x1.
    destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf].
    destruct xp; cbn; congruence.
Qed.

Lemma arrival_on_notify_ext : forall I x sb r, arrival_ext I true x (on_notify I x sb r).
Proof.
  intros. destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf].
  unfold on_notify, apply_sample, after_sample, issue_sample, issue, link_of, split,
    violate, close, finish.
  arrival_ext_by.
Qed.

Lemma arrival_on_cancel_ext : forall I x sb, arrival_ext I true x (on_cancel I x sb).
Proof.
  intros. destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf].
  unfold on_cancel, issue_sample, issue, finish. arrival_ext_by.
Qed.

Lemma arrival_issue_op_ext : forall I x f tok op, arrival_ext I true x (issue_op I x f tok op).
Proof.
  intros. destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf].
  unfold issue_op, issue, split, finish. arrival_ext_by.
Qed.

Lemma arrival_on_foreign_ext : forall I x fi, arrival_ext I false x (on_foreign x fi).
Proof.
  intros. destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf].
  unfold on_foreign, violate, close. arrival_ext_by.
Qed.

Lemma arrival_finish_verdict_ext : forall I x, arrival_ext I false x (finish x (verdict x)).
Proof.
  intros. destruct x as [xp xq xsb xaw xw xh xl xn xc xd xlv xre xv xt xpr xmi xf].
  unfold finish, verdict. arrival_ext_by.
Qed.

