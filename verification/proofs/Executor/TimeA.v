(** * The invariant behind P3, P7, P8 and P9: what each await can still lead to.

    For each fiber [f] and token [tok], the trace after the last start of [tok] by [f], and
    after the last command issued for it, determines what the state may still do for that
    await. A sleep is a chain: it waits for the slot, or one link is subscribed, or the
    sample after a link is pending, or its delivery is queued with every chunk credited, or
    nothing more can be delivered for it. A delivery is queued only after a sample that
    follows the await's last command; a cancellation only after a sample that credits
    nothing, or before any command. These facts rest on the single subscription and on the
    fact taken from I4 that no token is started twice. *)

From Coq Require Import List ZArith Bool Arith Lia Sorting.
From Durable Require Import Runtime Exec Rev3 Statements TimeBase TimeStep TimeL.
Import ListNotations.
Open Scope Z_scope.

(** ** What the invariant says *)

(** Fiber [f] waits for the slot for its operation [op] on [tok]. *)
Definition time_waiting (f : FiberId) (tok : Token) (op : Op) (x : XState) : Prop :=
  (exists mid, time_after_last (time_is_start f tok) (trace x) = Some (AStart f tok op, mid)
               /\ existsb time_is_sample mid = false) /\
  existsb (time_is_owned f tok) (trace x) = false /\
  awaiter x = Some (f, tok) /\ time_idle (sub x) = true /\
  time_nodel f tok (queue x) /\ ~ In (DeliverCancel f tok) (queue x).

(** No chunk has been credited to the await since its last command. *)
Definition time_since_credits (f : FiberId) (tok : Token) (t : list Action) : Prop :=
  match time_after_last (time_is_owned f tok) t with
  | Some (_, s) => credits f tok s = []
  | None => True
  end.

(** The subscription belongs to the await of [tok] by [f]: it was started, a command was
    issued for it since, and nothing has been credited since its last command. *)
Definition time_refd (f : FiberId) (tok : Token) (x : XState) : Prop :=
  (exists op mid, time_after_last (time_is_start f tok) (trace x) = Some (AStart f tok op, mid)
                  /\ existsb (time_is_owned f tok) mid = true) /\
  time_since_credits f tok (trace x).

(** P7's condition: a sample follows the await's last command. *)
Definition time_p7_ok (f : FiberId) (tok : Token) (t : list Action) : Prop :=
  match time_after_last (time_is_owned f tok) t with
  | Some (_, s) => existsb time_is_sample s = true
  | None => True
  end.

(** P8's first condition: a sample that credits nothing follows the last command, and no
    sample since it credits a chunk to the await. *)
Definition time_p8a_ok (f : FiberId) (tok : Token) (t : list Action) : Prop :=
  match time_after_last (time_is_owned f tok) t with
  | Some (_, s) => existsb time_is_plain s = true /\ credits f tok s = []
  | None => True
  end.

(** P8's second condition: with no command since the start, no sample since it either. *)
Definition time_p8b_ok (f : FiberId) (tok : Token) (t : list Action) : Prop :=
  match time_after_last (time_is_start f tok) t with
  | Some (_, mid) => existsb time_is_cmd mid = false -> existsb time_is_sample mid = false
  | None => True
  end.

(** P3's and P9's claim for a delivered operation [op], with [cr] the chunks credited
    since its start. *)
Definition time_sleep_claim (op : Op) (cr : list Z) : Prop :=
  match op with
  | OSleep (Millis d) => 0 < d -> time_sum cr = d /\ time_bounds cr
  | OSleep Forever => False
  | ORun _ _ => True
  end.

Definition time_p3_ok (f : FiberId) (tok : Token) (t : list Action) : Prop :=
  match time_after_last (time_is_start f tok) t with
  | Some (AStart _ _ op, mid) => time_sleep_claim op (credits f tok mid)
  | _ => True
  end.

(** What must hold of the trace before each delivery and each cancellation. *)
Definition time_claim_at (pre : list Action) (a : Action) : Prop :=
  match a with
  | ADelivered f tok _ => time_p3_ok f tok pre /\ time_p7_ok f tok pre
  | ACancelled f tok => time_p8a_ok f tok pre /\ time_p8b_ok f tok pre
  | _ => True
  end.

(** Where a sleep [op] started by [f] on [tok] stands, with [mid] the trace since. *)
Definition time_ld (f : FiberId) (tok : Token) (op : Op) (mid : list Action) (x : XState)
    : Prop :=
  time_bounds (credits f tok mid) /\
  (phase x = PDone
   \/ (waiter x = Some (f, tok, op) /\ credits f tok mid = [])
   \/ (exists c d k rest, sub x = Some (SOp c f tok (OSleep d) k rest) /\
         1 <= k <= max_chunk /\ time_chain_ok op (credits f tok mid) k rest /\
         time_nodel f tok (queue x))
   \/ (exists c k rest, sub x = Some (SSample c (FLink f tok k rest)) /\
         1 <= k <= max_chunk /\ time_chain_ok op (credits f tok mid) k rest /\
         time_nodel f tok (queue x))
   \/ (time_total_ok op (credits f tok mid) /\ time_sub_live f tok (sub x) = false /\
       time_waiter_is f tok (waiter x) = false)
   \/ (time_nodel f tok (queue x) /\ time_sub_live f tok (sub x) = false /\
       time_waiter_is f tok (waiter x) = false)).

Definition time_ldinv (f : FiberId) (tok : Token) (x : XState) : Prop :=
  match time_after_last (time_is_start f tok) (trace x) with
  | Some (AStart _ _ op, mid) => time_sleepy op -> time_ld f tok op mid x
  | _ => True
  end.

Record time_inva (x : XState) : Prop := {
  ta_r1 : forall f tok o, In (Deliver f tok o) (queue x) ->
    existsb (time_is_start f tok) (trace x) = true;
  ta_r2 : forall f tok, In (DeliverCancel f tok) (queue x) ->
    existsb (time_is_start f tok) (trace x) = true;
  ta_r3 : forall f tok op, waiter x = Some (f, tok, op) -> time_waiting f tok op x;
  ta_r4 : forall f tok, time_sub_refs f tok (sub x) = true -> time_refd f tok x;
  ta_owned : forall f tok, existsb (time_is_owned f tok) (trace x) = true ->
    existsb (time_is_start f tok) (trace x) = true;
  ta_ld : forall f tok, time_ldinv f tok x;
  ta_p7 : forall f tok o, In (Deliver f tok o) (queue x) -> time_p7_ok f tok (trace x);
  ta_p8 : forall f tok, In (DeliverCancel f tok) (queue x) ->
    time_p8a_ok f tok (trace x) /\ time_p8b_ok f tok (trace x);
  ta_claims : time_claims time_claim_at (trace x)
}.

(** ** Appending actions *)

Lemma time_after_last_ext : forall p t new,
  existsb p new = false ->
  time_after_last p (t ++ new) =
  match time_after_last p t with Some (b, s) => Some (b, s ++ new) | None => None end.
Proof.
  intros p t new. induction new as [|a new IH] using rev_ind; intros N.
  - rewrite app_nil_r. destruct (time_after_last p t) as [[b s]|]; rewrite ?app_nil_r;
    reflexivity.
  - rewrite existsb_app in N. apply orb_false_iff in N as [N1 N2]. simpl in N2.
    rewrite orb_false_r in N2. rewrite app_assoc, time_after_last_snoc, N2, IH by exact N1.
    destruct (time_after_last p t) as [[b s]|]; [|reflexivity]. rewrite app_assoc.
    reflexivity.
Qed.

(** An action that changes no await's standing: not a start, not a command issued for an
    await, not a sample. Deliveries and cancellations are allowed; their claims are
    checked separately. *)
Definition time_neutral (a : Action) : bool :=
  match a with
  | AStart _ _ _ | ASampled _ _ _ _ | ACommand _ _ (Some _) => false
  | _ => true
  end.

Lemma time_neutral_start : forall f tok new,
  forallb time_neutral new = true -> existsb (time_is_start f tok) new = false.
Proof.
  intros f tok new N. induction new as [|a new IH]; [reflexivity|].
  cbn in N |- *. apply andb_true_iff in N as [N1 N2]. rewrite IH by exact N2.
  destruct a; try discriminate; reflexivity.
Qed.

Lemma time_neutral_owned : forall f tok new,
  forallb time_neutral new = true -> existsb (time_is_owned f tok) new = false.
Proof.
  intros f tok new N. induction new as [|a new IH]; [reflexivity|].
  cbn in N |- *. apply andb_true_iff in N as [N1 N2]. rewrite IH by exact N2.
  destruct a as [| | ? ? [[? ?]|] | | | | | | | | |]; try discriminate; reflexivity.
Qed.

Lemma time_neutral_sample : forall new,
  forallb time_neutral new = true -> existsb time_is_sample new = false.
Proof.
  intros new N. induction new as [|a new IH]; [reflexivity|].
  cbn in N |- *. apply andb_true_iff in N as [N1 N2]. rewrite IH by exact N2.
  destruct a; try discriminate; reflexivity.
Qed.

Lemma time_neutral_credits : forall f tok new,
  forallb time_neutral new = true -> credits f tok new = [].
Proof.
  intros f tok new N. induction new as [|a new IH]; [reflexivity|].
  cbn in N. apply andb_true_iff in N as [N1 N2]. unfold credits in *. cbn.
  rewrite IH by exact N2. destruct a; try discriminate; reflexivity.
Qed.

Lemma time_existsb_app_true : forall (p : Action -> bool) a b,
  existsb p a = true -> existsb p (a ++ b) = true.
Proof. intros. rewrite existsb_app, H. reflexivity. Qed.

Lemma time_credits_nil_samples : forall f tok t,
  existsb time_is_sample t = false -> credits f tok t = [].
Proof.
  intros f tok t. induction t as [|a t IH]; [reflexivity|]. cbn.
  intros H. apply orb_false_iff in H as [H1 H2]. unfold credits in *. cbn.
  rewrite IH by exact H2. destruct a; try discriminate; reflexivity.
Qed.

Lemma time_idle_live : forall f tok s, time_idle s = true -> time_sub_live f tok s = false.
Proof. intros f tok [[| c [] |]|]; cbn; try discriminate; reflexivity. Qed.

Lemma time_idle_refs : forall f tok s, time_idle s = true -> time_sub_refs f tok s = false.
Proof. intros f tok [[| c [] |]|]; cbn; try discriminate; reflexivity. Qed.

Lemma time_ld_frame : forall f tok op mid mid' x x',
  time_ld f tok op mid x -> credits f tok mid' = credits f tok mid ->
  (phase x = PDone -> phase x' = PDone) ->
  (sub x' = sub x \/ time_idle (sub x') = true) ->
  (waiter x' = waiter x \/ waiter x' = None) ->
  (time_nodel f tok (queue x) -> time_nodel f tok (queue x')) ->
  (forall op', waiter x = Some (f, tok, op') -> time_nodel f tok (queue x)) ->
  (forall w, waiter x = Some w -> time_idle (sub x) = true) ->
  time_ld f tok op mid' x'.
Proof.
  intros f tok op mid mid' x x' [B L] C P S W N Wn Wi. unfold time_ld. rewrite C.
  split; [exact B|].
  assert (Hl : time_sub_live f tok (sub x) = false -> time_sub_live f tok (sub x') = false).
  { intros H. destruct S as [-> | S]; [exact H|apply time_idle_live; exact S]. }
  assert (Hw : time_waiter_is f tok (waiter x) = false ->
               time_waiter_is f tok (waiter x') = false).
  { intros H. destruct W as [-> | ->]; [exact H|reflexivity]. }
  assert (Wnone : forall s, sub x = Some s -> time_idle (Some s) = false -> waiter x = None).
  { intros s E I0. destruct (waiter x) as [w|] eqn:Ew; [|reflexivity].
    specialize (Wi w eq_refl). rewrite E in Wi. congruence. }
  destruct L as [PD|[[S1 C1]|[S2|[S3|[Fz|Dd]]]]].
  - left. apply P. exact PD.
  - destruct W as [W|W].
    + right; left. rewrite W. split; assumption.
    + right; right; right; right; right. split; [apply N; eapply Wn; exact S1|].
      split; [|rewrite W; reflexivity]. apply Hl. apply time_idle_live. eapply Wi. exact S1.
  - destruct S2 as [c [d [k [rest [E [K [Ch Nd]]]]]]]. destruct S as [S|S].
    + right; right; left. exists c, d, k, rest. rewrite S. auto.
    + right; right; right; right; right. split; [apply N; exact Nd|].
      split; [apply time_idle_live; exact S|].
      rewrite (Wnone _ E eq_refl) in W. destruct W as [-> | ->]; reflexivity.
  - destruct S3 as [c [k [rest [E [K [Ch Nd]]]]]]. destruct S as [S|S].
    + right; right; right; left. exists c, k, rest. rewrite S. auto.
    + right; right; right; right; right. split; [apply N; exact Nd|].
      split; [apply time_idle_live; exact S|].
      rewrite (Wnone _ E eq_refl) in W. destruct W as [-> | ->]; reflexivity.
  - destruct Fz as [T [Lv Wv]]. right; right; right; right; left. auto.
  - destruct Dd as [Nd [Lv Wv]]. right; right; right; right; right. auto.
Qed.

Lemma time_inva_frame : forall x x' new,
  time_inva x ->
  trace x' = trace x ++ new ->
  forallb time_neutral new = true ->
  time_claims time_claim_at (trace x') ->
  (forall t, In t (queue x') -> In t (queue x) \/ is_delivery t = false) ->
  (sub x' = sub x \/ time_idle (sub x') = true) ->
  (forall w, waiter x' = Some w -> waiter x = Some w /\ awaiter x' = awaiter x) ->
  (phase x = PDone -> phase x' = PDone) ->
  time_inva x'.
Proof.
  intros x x' new Hx T N Cl Q S W P.
  assert (Ns : forall f tok, existsb (time_is_start f tok) new = false)
    by (intros; apply time_neutral_start; exact N).
  assert (No : forall f tok, existsb (time_is_owned f tok) new = false)
    by (intros; apply time_neutral_owned; exact N).
  assert (Nsa : existsb time_is_sample new = false) by (apply time_neutral_sample; exact N).
  assert (Ncr : forall f tok, credits f tok new = []) by (intros; apply time_neutral_credits; exact N).
  assert (Nd : forall f tok, time_nodel f tok (queue x) -> time_nodel f tok (queue x')).
  { intros f tok H o I0. destruct (Q _ I0) as [I1|I1]; [exact (H o I1)|discriminate]. }
  assert (Qd : forall t, In t (queue x') -> is_delivery t = true -> In t (queue x)).
  { intros t I0 D. destruct (Q t I0) as [I1|I1]; [exact I1|congruence]. }
  assert (W' : waiter x' = waiter x \/ waiter x' = None).
  { destruct (waiter x') as [w|] eqn:E; [left; rewrite (proj1 (W w eq_refl)); reflexivity|].
    right; reflexivity. }
  constructor; unfold time_waiting, time_refd, time_since_credits, time_ldinv, time_p7_ok,
    time_p8a_ok, time_p8b_ok; rewrite ?T.
  - intros f tok o I0. apply time_existsb_app_true. apply (ta_r1 x Hx f tok o).
    apply Qd; [exact I0|reflexivity].
  - intros f tok I0. apply time_existsb_app_true. apply (ta_r2 x Hx f tok).
    apply Qd; [exact I0|reflexivity].
  - intros f tok op E. destruct (W _ E) as [E0 A0].
    destruct (ta_r3 x Hx f tok op E0) as [[mid [M1 M2]] [O [A [Id [Dl Dc]]]]].
    split; [|split; [|split; [|split; [|split]]]].
    + exists (mid ++ new). rewrite time_after_last_ext, M1 by apply Ns. split; [reflexivity|].
      rewrite existsb_app, M2, Nsa. reflexivity.
    + rewrite existsb_app, O, No. reflexivity.
    + rewrite A0. exact A.
    + destruct S as [-> | S]; assumption.
    + apply Nd. exact Dl.
    + intros I0. apply Dc. apply Qd; [exact I0|reflexivity].
  - intros f tok R. assert (S' : sub x' = sub x).
    { destruct S as [S|S]; [exact S|]. rewrite time_idle_refs in R by exact S. discriminate. }
    rewrite S' in R. destruct (ta_r4 x Hx f tok R) as [[op [mid [M1 M2]]] Sc]. split.
    + exists op, (mid ++ new). rewrite time_after_last_ext, M1 by apply Ns.
      split; [reflexivity|]. apply time_existsb_app_true. exact M2.
    + unfold time_since_credits in *. rewrite time_after_last_ext by apply No.
      destruct (time_after_last (time_is_owned f tok) (trace x)) as [[b s]|]; [|exact I].
      rewrite time_credits_app, Sc, Ncr. reflexivity.
  - intros f tok O. rewrite existsb_app, No, orb_false_r in O.
    apply time_existsb_app_true. apply (ta_owned x Hx f tok O).
  - intros f tok. pose proof (ta_ld x Hx f tok) as L. unfold time_ldinv in *.
    rewrite time_after_last_ext by apply Ns.
    destruct (time_after_last (time_is_start f tok) (trace x)) as [[b mid]|]; [|exact I].
    destruct b; try exact I. intros Sl. specialize (L Sl).
    apply (time_ld_frame f tok op mid (mid ++ new) x x' L); auto.
    + rewrite time_credits_app, Ncr, app_nil_r. reflexivity.
    + intros op' E. exact (proj1 (proj2 (proj2 (proj2 (proj2 (ta_r3 x Hx f tok op' E)))))).
    + intros [[f' tok'] op'] E. exact (proj1 (proj2 (proj2 (proj2 (ta_r3 x Hx f' tok' op' E))))).
  - intros f tok o I0. pose proof (ta_p7 x Hx f tok o (Qd _ I0 eq_refl)) as H.
    unfold time_p7_ok in *. rewrite time_after_last_ext by apply No.
    destruct (time_after_last (time_is_owned f tok) (trace x)) as [[b s]|]; [|exact I].
    apply time_existsb_app_true. exact H.
  - intros f tok I0. destruct (ta_p8 x Hx f tok (Qd _ I0 eq_refl)) as [Ha Hb]. split.
    + unfold time_p8a_ok in *. rewrite time_after_last_ext by apply No.
      destruct (time_after_last (time_is_owned f tok) (trace x)) as [[b s]|]; [|exact I].
      destruct Ha as [Ha1 Ha2]. split; [apply time_existsb_app_true; exact Ha1|].
      rewrite time_credits_app, Ha2, Ncr. reflexivity.
    + unfold time_p8b_ok in *. rewrite time_after_last_ext by apply Ns.
      destruct (time_after_last (time_is_start f tok) (trace x)) as [[b mid]|]; [|exact I].
      rewrite !existsb_app, Nsa, orb_false_r. intros Hc. apply orb_false_iff in Hc as [Hc _].
      apply Hb. exact Hc.
  - rewrite <- T. exact Cl.
Qed.

(** Claims are kept when the new actions are neither deliveries nor cancellations. *)
Definition time_quiet (a : Action) : bool :=
  match a with ADelivered _ _ _ | ACancelled _ _ => false | _ => true end.

Lemma time_claims_quiet : forall t new,
  time_claims time_claim_at t -> forallb time_quiet new = true ->
  time_claims time_claim_at (t ++ new).
Proof.
  intros t new C N. induction new as [|a new IH] using rev_ind;
    [rewrite app_nil_r; exact C|].
  rewrite forallb_app in N. apply andb_true_iff in N as [N1 N2]. cbn in N2.
  rewrite andb_true_r in N2. rewrite app_assoc. apply time_claims_snoc; [apply IH; exact N1|].
  destruct a; try discriminate; exact I.
Qed.

Lemma time_forallb_and : forall (p q : Action -> bool) l,
  forallb (fun a => p a && q a) l = true -> forallb p l = true /\ forallb q l = true.
Proof.
  intros p q l. induction l as [|a l IH]; [auto|]. cbn. intros H.
  apply andb_true_iff in H as [H1 H2]. apply andb_true_iff in H1 as [H1 H3].
  rewrite H1, H3. apply IH. exact H2.
Qed.

(** The frame for actions that are neither deliveries nor cancellations. *)
Lemma time_inva_frame_quiet : forall x x' new,
  time_inva x ->
  trace x' = trace x ++ new ->
  forallb (fun a => time_neutral a && time_quiet a) new = true ->
  (forall t, In t (queue x') -> In t (queue x) \/ is_delivery t = false) ->
  (sub x' = sub x \/ time_idle (sub x') = true) ->
  (forall w, waiter x' = Some w -> waiter x = Some w /\ awaiter x' = awaiter x) ->
  (phase x = PDone -> phase x' = PDone) ->
  time_inva x'.
Proof.
  intros x x' new Hx T N Q S W P.
  destruct (time_forallb_and _ _ _ N) as [N1 N2].
  apply (time_inva_frame x x' new Hx T N1); auto.
  rewrite T. apply time_claims_quiet; [apply (ta_claims x Hx)|exact N2].
Qed.

(** The common frame: no new action, and only fields other than the queue, subscription,
    waiter, awaiter and phase change. *)
Lemma time_inva_same : forall x x',
  time_inva x -> trace x' = trace x -> queue x' = queue x -> sub x' = sub x ->
  waiter x' = waiter x -> awaiter x' = awaiter x -> phase x' = phase x -> time_inva x'.
Proof.
  intros x x' Hx T Q S W A P. apply (time_inva_frame_quiet x x' [] Hx); auto.
  - rewrite T, app_nil_r. reflexivity.
  - intros t I0. rewrite Q in I0. auto.
  - intros w E. rewrite W in E. auto.
  - rewrite P. auto.
Qed.
