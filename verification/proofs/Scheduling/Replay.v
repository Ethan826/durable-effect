(** * S2, replay determinism.

    Two environments that agree on a journal prefix (the first [ops] operation results and
    the first [samples] samples) give replays that take the same steps until one of them
    consumes an entry beyond the prefix. From then on that replay's trace, cut at the replay
    point (D9), never changes, and it is a prefix of the other's cut. So the cuts of both
    replays, at any lengths, are prefixes of one list. A run under any arrival schedule is a
    replay up to the micro-step counter (Arrival.v), which gives S2. *)

From Coq Require Import List ZArith Bool Arith Lia.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model Executor Statements ExecutorLemmas Arrival.
Import ListNotations.

(** ** Lists *)

Lemma prefix_common : forall {X} (a b c : list X),
  prefix a c -> prefix b c -> compatible a b.
Proof.
  intros X a b c [r1 Hr1] [r2 Hr2]. rewrite Hr1 in Hr2.
  destruct (app_eq_app _ _ _ _ Hr2) as [l [[-> _]|[-> _]]];
    [right|left]; exists l; reflexivity.
Qed.

Section Cut.

Variables ops samples : nat.

(** Whether a trace consumes a journal entry beyond the prefix. *)
Definition beyond (l : list Action) : bool := existsb (consumes_beyond ops samples) l.

Lemma beyond_app : forall l r, beyond (l ++ r) = beyond l || beyond r.
Proof. intros l r. apply existsb_app. Qed.

Lemma cut_clean : forall l, beyond l = false -> cut ops samples l = l.
Proof.
  induction l as [|a l IH]; intros H; [reflexivity|].
  unfold beyond in H. simpl in H. apply orb_false_iff in H as [Ha Hl].
  simpl. rewrite Ha, IH; [reflexivity|exact Hl].
Qed.

Lemma cut_app_clean : forall l r,
  beyond l = false -> cut ops samples (l ++ r) = l ++ cut ops samples r.
Proof.
  induction l as [|a l IH]; intros r H; [reflexivity|].
  unfold beyond in H. simpl in H. apply orb_false_iff in H as [Ha Hl].
  simpl. rewrite Ha, IH; [reflexivity|exact Hl].
Qed.

Lemma cut_app_dirty : forall l r,
  beyond l = true -> cut ops samples (l ++ r) = cut ops samples l.
Proof.
  induction l as [|a l IH]; intros r H; [discriminate|].
  unfold beyond in H. simpl in H. simpl.
  destruct (consumes_beyond ops samples a); [reflexivity|].
  rewrite IH; [reflexivity|exact H].
Qed.

Lemma cut_mono : forall l l', prefix l l' -> prefix (cut ops samples l) (cut ops samples l').
Proof.
  intros l l' [r ->]. destruct (beyond l) eqn:H.
  - rewrite cut_app_dirty by exact H. apply prefix_refl.
  - rewrite cut_app_clean, cut_clean by exact H. apply prefix_app.
Qed.

(** Once a trace consumes an entry beyond the prefix, its cut never changes. *)
Lemma cut_frozen : forall l l',
  beyond l = true -> prefix l l' -> cut ops samples l' = cut ops samples l.
Proof. intros l l' H [r ->]. apply cut_app_dirty. exact H. Qed.

Lemma beyond_mono : forall l l', beyond l = true -> prefix l l' -> beyond l' = true.
Proof. intros l l' H [r ->]. rewrite beyond_app, H. reflexivity. Qed.

End Cut.

(** ** Environments that agree on the prefix *)

(** [run_fiber] and [run_head] read the environment only through the random stream. *)
Lemma run_fiber_env : forall pol P E1 E2 fuel n st f,
  (forall k, random_of E1 k = random_of E2 k) ->
  run_fiber pol P E1 fuel n st f = run_fiber pol P E2 fuel n st f.
Proof.
  intros pol P E1 E2 fuel n st f Hr.
  pose proof (run_fiber_set_micro pol P E1 E2 Hr fuel n st f (micro st)) as H1.
  pose proof (run_fiber_set_micro pol P E2 E2 (fun _ => eq_refl) fuel n st f (micro st))
    as H2.
  rewrite set_micro_id in H1, H2. rewrite H1, <- H2. reflexivity.
Qed.

Lemma run_head_env : forall pol P E1 E2 st h rest,
  (forall k, random_of E1 k = random_of E2 k) ->
  run_head pol P E1 st h rest = run_head pol P E2 st h rest.
Proof.
  intros pol P E1 E2 st h rest Hr. unfold run_head.
  destruct (find_fiber h _) as [f|]; [destruct (status f)|];
    rewrite ?(run_fiber_env _ _ E1 E2 _ _ _ _ Hr); reflexivity.
Qed.

Lemma resume_trace : forall st h o, trace (resume st h o) = trace st.
Proof. intros st h o. unfold resume. destruct (find_fiber h (fibers st)); reflexivity. Qed.

(** A delivery adds the sample's command and value, then an action that consumes the
    operation (its delivery or its cancellation) or, for an uncancelled sleep, either that or
    the next link of the chain. *)
Lemma deliver_shape : forall E st aw, exists a r,
  trace (deliver E st aw)
    = trace st ++ SampleCommand (next_sample st)
        :: Sampled (next_sample st) (sample_value (sample_of E (next_sample st))) :: a :: r /\
  ((exists h o, a = Delivered (awaited_op aw) h o) \/
   (exists h, a = CancelDelivered (awaited_op aw) h) \/
   (cancelled_at E (awaited_op aw) = false /\
    exists h op c rest, aw = AwaitSleep h op c rest)).
Proof.
  intros E st aw. unfold deliver, cancel.
  destruct aw as [h op|h op c rest]; destruct (cancelled_at E op) eqn:Hc.
  - match goal with |- context [interrupt_fiber ?X h] =>
      destruct (interrupt_fiber_trace X h) as [-> | ->] end;
      do 2 eexists; (split; [|right; left; exists h; reflexivity]);
      cbn [trace emit update take_sample]; repeat rewrite <- app_assoc; reflexivity.
  - rewrite resume_trace. do 2 eexists.
    split; [|left; do 2 eexists; reflexivity].
    cbn [trace emit update take_sample]; repeat rewrite <- app_assoc; reflexivity.
  - match goal with |- context [interrupt_fiber ?X h] =>
      destruct (interrupt_fiber_trace X h) as [-> | ->] end;
      do 2 eexists; (split; [|right; left; exists h; reflexivity]);
      cbn [trace emit update take_sample]; repeat rewrite <- app_assoc; reflexivity.
  - destruct rest as [|d|]; [rewrite resume_trace| |]; try destruct (d <=? max_chunk)%Z;
      do 2 eexists;
      (split; [ cbn [trace emit update take_sample]; repeat rewrite <- app_assoc; reflexivity
              | right; right; split; [exact Hc|do 4 eexists; reflexivity] ]).
Qed.

Lemma deliver_env : forall E1 E2 st aw,
  outcome_of E1 (awaited_op aw) = outcome_of E2 (awaited_op aw) ->
  cancelled_at E1 (awaited_op aw) = cancelled_at E2 (awaited_op aw) ->
  sample_of E1 (next_sample st) = sample_of E2 (next_sample st) ->
  deliver E1 st aw = deliver E2 st aw.
Proof.
  intros E1 E2 st [h op|h op c rest] Ho Hc Hs; unfold deliver, take_sample; cbv zeta;
    simpl in Ho, Hc; rewrite ?Ho, Hc, Hs; reflexivity.
Qed.

(** An uncancelled sleep's delivery does not read the operation's outcome. *)
Lemma deliver_sleep_env : forall E1 E2 st h op c rest,
  cancelled_at E1 op = cancelled_at E2 op ->
  sample_of E1 (next_sample st) = sample_of E2 (next_sample st) ->
  deliver E1 st (AwaitSleep h op c rest) = deliver E2 st (AwaitSleep h op c rest).
Proof.
  intros E1 E2 st h op c rest Hc Hs. unfold deliver, take_sample. cbv zeta.
  rewrite Hc, Hs. reflexivity.
Qed.

(** ** One step of two replays *)

Section Diverge.

Variables ops samples : nat.

Lemma cut_cons_clean : forall a l, consumes_beyond ops samples a = false ->
  cut ops samples (a :: l) = a :: cut ops samples l.
Proof. intros a l H. simpl. rewrite H. reflexivity. Qed.

Lemma cut_cons_dirty : forall a l, consumes_beyond ops samples a = true ->
  cut ops samples (a :: l) = [].
Proof. intros a l H. simpl. rewrite H. reflexivity. Qed.

(** Two traces that agree up to an action that consumes an entry beyond the prefix: the
    first's cut ends before that action, and the second's cut extends it. *)
Lemma diverge_lists : forall T x y a r a' r',
  beyond ops samples T = false -> consumes_beyond ops samples x = false ->
  consumes_beyond ops samples y = false -> consumes_beyond ops samples a = true ->
  beyond ops samples (T ++ x :: y :: a :: r) = true /\
  prefix (cut ops samples (T ++ x :: y :: a :: r))
         (cut ops samples (T ++ x :: y :: a' :: r')).
Proof.
  intros T x y a r a' r' HT Hx Hy Ha. split.
  - rewrite beyond_app, HT. unfold beyond. simpl. rewrite Hx, Hy, Ha. reflexivity.
  - rewrite !cut_app_clean by exact HT.
    rewrite !(cut_cons_clean x) by exact Hx. rewrite !(cut_cons_clean y) by exact Hy.
    rewrite (cut_cons_dirty a) by exact Ha.
    exists (cut ops samples (a' :: r')). rewrite <- app_assoc. reflexivity.
Qed.

(** Two traces whose sample is beyond the prefix: both cuts end before it. *)
Lemma sample_lists : forall T x y r y' r',
  beyond ops samples T = false -> consumes_beyond ops samples x = false ->
  consumes_beyond ops samples y = true -> consumes_beyond ops samples y' = true ->
  beyond ops samples (T ++ x :: y :: r) = true /\
  prefix (cut ops samples (T ++ x :: y :: r)) (cut ops samples (T ++ x :: y' :: r')).
Proof.
  intros T x y r y' r' HT Hx Hy Hy'. split.
  - rewrite beyond_app, HT. unfold beyond. simpl. rewrite Hx, Hy. reflexivity.
  - rewrite !cut_app_clean by exact HT. rewrite !(cut_cons_clean x) by exact Hx.
    rewrite (cut_cons_dirty y) by exact Hy. rewrite (cut_cons_dirty y') by exact Hy'.
    apply prefix_refl.
Qed.

(** The two replays' deliveries are equal, or one consumes an entry beyond the prefix and
    its cut is a prefix of the other's. *)
Definition diverges (t1 t2 : list Action) : Prop :=
  beyond ops samples t1 = true /\ prefix (cut ops samples t1) (cut ops samples t2).

Lemma deliver_diverge : forall E1 E2 st aw,
  agree_upto ops samples E1 E2 -> beyond ops samples (trace st) = false ->
  deliver E1 st aw = deliver E2 st aw \/
  diverges (trace (deliver E1 st aw)) (trace (deliver E2 st aw)) \/
  diverges (trace (deliver E2 st aw)) (trace (deliver E1 st aw)).
Proof.
  intros E1 E2 st aw (Ho & Hc & Hs & _ & _) Hcl. unfold diverges.
  destruct (deliver_shape E1 st aw) as (a1 & r1 & T1 & K1).
  destruct (deliver_shape E2 st aw) as (a2 & r2 & T2 & K2).
  rewrite T1, T2.
  destruct (Nat.ltb (next_sample st) samples) eqn:Hi.
  2: { apply Nat.ltb_ge in Hi. assert (Hl : Nat.leb samples (next_sample st) = true)
         by (apply Nat.leb_le; exact Hi).
       right; left. apply sample_lists; [exact Hcl|reflexivity|exact Hl|exact Hl]. }
  apply Nat.ltb_lt in Hi. rewrite (Hs _ Hi) in T1 |- *.
  assert (Hl : Nat.leb samples (next_sample st) = false) by (apply Nat.leb_gt; exact Hi).
  destruct (Nat.ltb (awaited_op aw) ops) eqn:Hop.
  { apply Nat.ltb_lt in Hop. left. apply deliver_env; auto. }
  apply Nat.ltb_ge in Hop.
  assert (Hlo : Nat.leb ops (awaited_op aw) = true) by (apply Nat.leb_le; exact Hop).
  destruct K1 as [(h & o & ->)|[(h & ->)|(Hc1 & h & op & c & rest & Haw)]].
  1, 2: right; left; apply diverge_lists; auto.
  destruct K2 as [(h' & o & ->)|[(h' & ->)|(Hc2 & h' & op' & c' & rest' & _)]].
  1, 2: right; right; apply diverge_lists; auto.
  left. subst aw. apply deliver_sleep_env; [simpl in Hc1, Hc2; congruence|apply Hs, Hi].
Qed.

Lemma step_diverge : forall pol P E1 E2 st,
  agree_upto ops samples E1 E2 -> finished st = None -> beyond ops samples (trace st) = false ->
  step pol P E1 arrived no_outside_resumes st = step pol P E2 arrived no_outside_resumes st \/
  diverges (trace (step pol P E1 arrived no_outside_resumes st))
           (trace (step pol P E2 arrived no_outside_resumes st)) \/
  diverges (trace (step pol P E2 arrived no_outside_resumes st))
           (trace (step pol P E1 arrived no_outside_resumes st)).
Proof.
  intros pol P E1 E2 st Hag Hn Hcl. pose proof Hag as (_ & _ & _ & Hr & He).
  unfold step. rewrite Hn. change (no_outside_resumes _) with (@None (nat * nat)).
  cbv iota. rewrite He.
  destruct (ends_at E2) as [[n how]|];
    [destruct (Nat.eqb n (progress st)); [left; reflexivity|]|];
    (destruct (queue st) as [|h rest]; [|left; apply run_head_env; exact Hr]);
    (destruct (awaited st) as [aw|]; [|left; reflexivity]);
    change (arrived (awaited_op aw) (micro st)) with true; cbv iota;
    rewrite !trace_tick;
    (destruct (deliver_diverge E1 E2 st aw Hag Hcl) as [H|[H|H]];
     [left; rewrite H; reflexivity|right; left; exact H|right; right; exact H]).
Qed.

End Diverge.

(** ** Two replays *)

(** The replays of two environments that agree on the prefix take the same steps without
    consuming an entry beyond it, or one of them at some point has, and its cut there is a
    prefix of the other's. *)
Lemma lockstep : forall pol P E1 E2 ops samples,
  agree_upto ops samples E1 E2 -> forall m,
  (replay pol P E1 m = replay pol P E2 m /\
   beyond ops samples (trace (replay pol P E1 m)) = false) \/
  (exists d, diverges ops samples (trace (replay pol P E1 d)) (trace (replay pol P E2 d))) \/
  (exists d, diverges ops samples (trace (replay pol P E2 d)) (trace (replay pol P E1 d))).
Proof.
  intros pol P E1 E2 ops samples Hag. pose proof Hag as (_ & _ & Hs & _ & _).
  induction m as [|m [[Heq Hcl]|IH]]; [| |right; exact IH].
  - change (replay pol P ?E 0) with (initial P E). unfold initial, diverges, beyond.
    destruct samples as [|samples].
    + right; left. exists 0%nat. split; [reflexivity|apply prefix_refl].
    + left. rewrite (Hs 0%nat) by lia. split; reflexivity.
  - rewrite !replay_S, <- Heq.
    destruct (finished (replay pol P E1 m)) as [e|] eqn:Hn.
    { left. rewrite !(step_finished _ _ _ _ _ _ e Hn). split; [reflexivity|exact Hcl]. }
    destruct (step_diverge ops samples pol P E1 E2 _ Hag Hn Hcl) as [H|[H|H]].
    + rewrite H. destruct (beyond ops samples (trace (step pol P E2 arrived
        no_outside_resumes (replay pol P E1 m)))) eqn:Hb.
      * right; left. exists (S m). rewrite !replay_S, <- Heq, H.
        split; [first [exact Hb|reflexivity]|apply prefix_refl].
      * left. split; reflexivity.
    + right; left. exists (S m). rewrite !replay_S, <- Heq. exact H.
    + right; right. exists (S m). rewrite !replay_S, <- Heq. exact H.
Qed.

(** A replay's cut after [m] steps is a prefix of the cut after any later step. *)
Lemma replay_cut_mono : forall pol P E ops samples m m', (m <= m')%nat ->
  prefix (cut ops samples (trace (replay pol P E m)))
         (cut ops samples (trace (replay pol P E m'))).
Proof. intros. apply cut_mono, replay_prefix. assumption. Qed.

(** If the first replay has consumed an entry beyond the prefix at step [d], every cut of it is
    a prefix of the second replay's cut at any step from [d] on. *)
Lemma frozen_below : forall pol P E1 E2 ops samples d m N,
  diverges ops samples (trace (replay pol P E1 d)) (trace (replay pol P E2 d)) ->
  (d <= N)%nat ->
  prefix (cut ops samples (trace (replay pol P E1 m)))
         (cut ops samples (trace (replay pol P E2 N))).
Proof.
  intros pol P E1 E2 ops samples d m N [Hb Hp] HN.
  eapply prefix_trans; [apply (replay_cut_mono _ _ _ _ _ m (m + d)); lia|].
  rewrite (cut_frozen _ _ _ _ Hb (replay_prefix _ _ _ d (m + d) ltac:(lia))).
  eapply prefix_trans; [exact Hp|apply replay_cut_mono; exact HN].
Qed.

Theorem s2 : S2.
Proof.
  intros P E1 E2 A1 A2 ops samples n1 n2 Hag _.
  destruct (stutter policy_v1 P E1 E1 A1 n1 (same_values_refl E1) eq_refl)
    as (m1 & j1 & H1).
  destruct (stutter policy_v1 P E2 E2 A2 n2 (same_values_refl E2) eq_refl)
    as (m2 & j2 & H2).
  unfold run. rewrite H1, H2, !trace_set_micro.
  destruct (lockstep policy_v1 P E1 E2 ops samples Hag (m1 + m2))
    as [[Heq _]|[(d & Hd)|(d & Hd)]].
  - apply (prefix_common _ _ (cut ops samples (trace (replay policy_v1 P E1 (m1 + m2))))).
    + apply replay_cut_mono. lia.
    + rewrite Heq. apply replay_cut_mono. lia.
  - apply (prefix_common _ _
      (cut ops samples (trace (replay policy_v1 P E2 (m1 + m2 + d))))).
    + apply (frozen_below _ _ _ _ _ _ d); [exact Hd|lia].
    + apply replay_cut_mono. lia.
  - apply (prefix_common _ _
      (cut ops samples (trace (replay policy_v1 P E1 (m1 + m2 + d))))).
    + apply replay_cut_mono. lia.
    + apply (frozen_below _ _ _ _ _ _ d); [exact Hd|lia].
Qed.
