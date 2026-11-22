(** * Micro-steps and the reachable-state invariants used by S4, S5 and S8.

    The first part lifts the generic preservation argument of SingleStepLemmas.v to a whole
    micro-step and to every reachable state. The second part gives the invariants. *)

From Coq Require Import List ZArith Bool Arith Lia.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model Executor Statements SingleStepLemmas.
Import ListNotations.
Open Scope Z_scope.

(** ** A micro-step, case by case *)

(** The work of a micro-step once no outside resume and no attempt end applies. *)
Definition turn (pol : Policy) (P : Program) (E : Env) (A : Arrival) (st : State) : State :=
  match queue st with
  | h :: rest => run_head pol P E st h rest
  | [] =>
      match awaited st with
      | Some aw => if A (awaited_op aw) (micro st) then tick (deliver E st aw) true
                   else tick st false
      | None => if root_done st then tick (finish st Succeeded) true
                else if blocked_is_violation pol then
                  tick (violate st BlockedWithNothingAwaited) true
                else tick st false
      end
  end.

Lemma step_unfold : forall pol P E A X st,
  finished st = None -> X (micro st) = None ->
  step pol P E A X st =
    match ends_at E with
    | Some (n, how) => if Nat.eqb n (progress st) then tick (end_attempt st how) true
                       else turn pol P E A st
    | None => turn pol P E A st
    end.
Proof.
  intros pol P E A X st Hf Hx. unfold step. rewrite Hf, Hx.
  destruct (ends_at E) as [[n how]|]; reflexivity.
Qed.

(** Without an outside resume at this micro-step, [X] plays no part. *)
Lemma step_no_resume : forall pol P E A X st,
  X (micro st) = None ->
  step pol P E A X st = step pol P E A no_outside_resumes st.
Proof.
  intros pol P E A X st Hx. unfold step.
  destruct (finished st); [reflexivity|]. rewrite Hx. reflexivity.
Qed.

Lemma step_finished : forall pol P E A X st e,
  finished st = Some e -> step pol P E A X st = st.
Proof. intros pol P E A X st e Hf. unfold step. rewrite Hf. reflexivity. Qed.

Section Lift.

Variable pol : Policy.
Variable Q : Inv.
Hypothesis HQ : closed pol Q.
Hypothesis HT : closed_turn Q.

Lemma turn_holds : forall P E A st, holds Q st -> holds Q (turn pol P E A st).
Proof.
  intros P E A st H. unfold turn.
  destruct (queue st) as [|h rest]; [|apply (run_head_holds _ _ HQ); exact H].
  destruct (awaited st) as [aw|] eqn:Ha.
  - destruct (A _ _); apply tick_holds; [|exact H].
    apply (deliver_holds _ _ HQ HT); assumption.
  - destruct (root_done st); [|destruct (blocked_is_violation pol)];
      apply tick_holds; try exact H.
    + apply (finish_holds _ _ HQ). exact H.
    + apply (violate_holds _ _ HQ); [discriminate | exact H].
Qed.

Lemma step_holds : forall P E A st,
  holds Q st -> holds Q (step pol P E A no_outside_resumes st).
Proof.
  intros P E A st H. destruct (finished st) as [e|] eqn:Hf.
  - rewrite (step_finished _ _ _ _ _ _ e Hf). exact H.
  - rewrite step_unfold by (exact Hf || reflexivity).
    destruct (ends_at E) as [[n how]|];
      [destruct (Nat.eqb n (progress st))|]; try (apply turn_holds; exact H).
    apply tick_holds. apply (end_attempt_holds _ _ HQ). exact H.
Qed.

Lemma iterate_holds : forall P E A k st,
  holds Q st -> holds Q (iterate pol P E A no_outside_resumes k st).
Proof.
  intros P E A k. induction k as [|k IH]; intros st H; [exact H|].
  apply IH. apply step_holds. exact H.
Qed.

Lemma reachable_holds : forall P E A k,
  (forall l, Q [] None 0%nat l) ->
  holds Q (iterate pol P E A no_outside_resumes k (initial P E)).
Proof.
  intros P E A k H0. apply iterate_holds. apply (init_holds _ _ HQ). exact H0.
Qed.

End Lift.

(** ** Lists *)

Lemma in_snoc : forall {X} (x a : X) tr, In x (tr ++ [a]) -> In x tr \/ x = a.
Proof.
  intros X x a tr H. apply in_app_or in H. destruct H as [H|[H|[]]]; auto.
Qed.

Lemma snoc_split : forall {X} (pre post tr : list X) c a,
  pre ++ c :: post = tr ++ [a] ->
  (post = [] /\ pre = tr /\ c = a) \/
  (exists post', post = post' ++ [a] /\ tr = pre ++ c :: post').
Proof.
  intros X pre post tr c a Heq.
  induction post as [|x post' _] using rev_ind.
  - left. apply app_inj_tail in Heq. destruct Heq as [-> ->]. auto.
  - right. exists post'. rewrite app_comm_cons, app_assoc in Heq.
    apply app_inj_tail in Heq. destruct Heq as [<- ->]. auto.
Qed.

Lemma cleared_some : forall aw h a, cleared aw h = Some a -> aw = Some a.
Proof.
  intros [b|] h a H; cbn in H; [|discriminate].
  destruct (Nat.eqb (awaited_handle b) h); [discriminate | exact H].
Qed.

(** ** S4: commands are single-awaited *)

(** A command for operation [op] of fiber [h] whose wait has not ended. *)
Definition open_in (tr : list Action) (op h : nat) : Prop :=
  exists pre c post, tr = pre ++ c :: post /\ command_of c = Some (op, h) /\
    forallb (fun x => negb (ends_wait op h x)) post = true.

Lemma open_nil : forall op h, ~ open_in [] op h.
Proof.
  intros op h (pre & c & post & Heq & _). exact (app_cons_not_nil _ _ _ Heq).
Qed.

Lemma open_cons : forall a tr op h, open_in tr op h -> open_in (a :: tr) op h.
Proof.
  intros a tr op h (pre & c & post & -> & Hc & Hf). exists (a :: pre), c, post. auto.
Qed.

Lemma open_snoc : forall tr a op h, open_in (tr ++ [a]) op h ->
  (open_in tr op h /\ ends_wait op h a = false) \/ command_of a = Some (op, h).
Proof.
  intros tr a op h (pre & c & post & Heq & Hc & Hf). symmetry in Heq.
  destruct (snoc_split _ _ _ _ _ Heq) as [(-> & -> & ->) | (post' & -> & ->)].
  - right. exact Hc.
  - left. rewrite forallb_app in Hf. apply andb_prop in Hf. destruct Hf as [Hf1 Hf2].
    split; [exists pre, c, post'; auto|].
    cbn in Hf2. destruct (ends_wait op h a); [discriminate | reflexivity].
Qed.

(** Appending one action keeps commands single-awaited when a command it adds belongs to
    the fiber of every open wait. *)
Lemma single_await_snoc : forall tr b,
  single_await tr ->
  (forall op' h', command_of b = Some (op', h') -> forall op h, open_in tr op h -> h' = h) ->
  single_await (tr ++ [b]).
Proof.
  intros tr b. induction tr as [|a rest IH]; intros H Hb.
  - cbn. destruct (command_of b) as [[op h]|]; [|exact I]. split; [|exact I].
    intros pre b0 post Heq. destruct (app_cons_not_nil _ _ _ Heq).
  - cbn in H |- *. destruct (command_of a) as [[op h]|] eqn:Ha.
    + destruct H as [H1 H2]. split.
      * intros pre b0 post Heq Hf op' h' Hc. symmetry in Heq.
        destruct (snoc_split _ _ _ _ _ Heq) as [(-> & -> & ->) | (post' & -> & ->)].
        -- apply (Hb op' h' Hc op h). exists [], a, rest. auto.
        -- exact (H1 pre b0 post' eq_refl Hf op' h' Hc).
      * apply IH; [exact H2|]. intros op' h' Hc op0 h0 Ho.
        apply (Hb op' h' Hc op0 h0). apply open_cons. exact Ho.
    + apply IH; [exact H|]. intros op' h' Hc op0 h0 Ho.
      apply (Hb op' h' Hc op0 h0). apply open_cons. exact Ho.
Qed.

(** Every open wait is the awaited operation, whose index is below the next one. *)
Definition W : Inv := fun tr aw n _ =>
  single_await tr /\
  (forall op h, open_in tr op h ->
     exists a, aw = Some a /\ awaited_handle a = h /\ awaited_op a = op) /\
  (forall a, aw = Some a -> (awaited_op a < n)%nat).

Lemma W_quiet : forall tr aw n l a,
  command_of a = None -> W tr aw n l -> W (tr ++ [a]) aw n l.
Proof.
  intros tr aw n l a Hc (H1 & H2 & H3). split; [|split; [|exact H3]].
  - apply single_await_snoc; [exact H1|]. intros op' h' Ha. congruence.
  - intros op h Ho. destruct (open_snoc _ _ _ _ Ho) as [[Ho' _]|Ha]; [|congruence].
    apply H2. exact Ho'.
Qed.

(** A command issued when nothing is awaited. *)
Lemma W_start : forall tr n l a h c,
  command_of a = Some (n, h) -> awaited_handle c = h -> awaited_op c = n ->
  W tr None n l -> W (tr ++ [a]) (Some c) (S n) l.
Proof.
  intros tr n l a h c Hc Hh Ho (H1 & H2 & H3).
  assert (Hn : forall op h', ~ open_in tr op h').
  { intros op h' Hop. destruct (H2 op h' Hop) as (b & Hb & _). discriminate. }
  split; [|split].
  - apply single_await_snoc; [exact H1|]. intros op' h' _ op h0 Hop.
    destruct (Hn _ _ Hop).
  - intros op h0 Hop. destruct (open_snoc _ _ _ _ Hop) as [[Ho' _]|Ha].
    + destruct (Hn _ _ Ho').
    + rewrite Hc in Ha. injection Ha as <- <-. exists c. auto.
  - intros b Hb. injection Hb as <-. rewrite Ho. lia.
Qed.

Lemma W_closed : forall pol, closed pol W.
Proof.
  intros pol. split.
  - intros tr aw n l a [Hc _]. apply W_quiet. exact Hc.
  - intros tr aw n l h (H1 & H2 & H3). split; [|split].
    + apply single_await_snoc; [exact H1|]. intros op' h' Ha. discriminate.
    + intros op h0 Hop. destruct (open_snoc _ _ _ _ Hop) as [[Ho' Hew]|Ha]; [|discriminate].
      destruct (H2 _ _ Ho') as (b & -> & Hb & Hob). exists b. split; [|auto].
      cbn in Hew |- *. rewrite Hb, Hew. reflexivity.
    + intros b Hb. apply H3. apply cleared_some with h. exact Hb.
  - intros tr n l h k a H. apply (W_start _ _ _ _ h); auto.
  - intros tr n l h c r _ H. apply (W_start _ _ _ _ h); auto.
Qed.

Lemma W_closed_turn : closed_turn W.
Proof.
  split.
  - intros tr aw n l i s floor _ H. apply W_quiet; [reflexivity|].
    apply W_quiet; [reflexivity | exact H].
  - intros tr aw n l o (H1 & H2 & H3). split; [|split].
    + apply single_await_snoc; [exact H1|]. intros op' h' Ha. discriminate.
    + intros op h Hop. destruct (open_snoc _ _ _ _ Hop) as [[Ho' Hew]|Ha]; [|discriminate].
      destruct (H2 _ _ Ho') as (b & Hb & _ & Hob). injection Hb as <-.
      cbn in Hew. rewrite Hob, Nat.eqb_refl in Hew. discriminate.
    + intros b Hb. discriminate.
  - intros tr h op c r n l c' r' _ (H1 & H2 & H3).
    assert (Hlt : (op < n)%nat) by exact (H3 _ eq_refl).
    split; [|split].
    + apply single_await_snoc; [exact H1|]. intros op' h' Ha op0 h0 Hop.
      cbn in Ha. injection Ha as _ <-.
      destruct (H2 _ _ Hop) as (b & Hb & Hh & _). injection Hb as <-. exact Hh.
    + intros op0 h0 Hop. destruct (open_snoc _ _ _ _ Hop) as [[Ho' Hew]|Ha].
      * destruct (H2 _ _ Ho') as (b & Hb & Hh & Hob). injection Hb as <-.
        cbn in Hh, Hob. subst h0 op0. cbn in Hew. rewrite Nat.eqb_refl in Hew.
        destruct (Nat.eqb op n) eqn:E; [apply Nat.eqb_eq in E; lia | discriminate].
      * cbn in Ha. injection Ha as <- <-. exists (AwaitSleep h n c' r'). auto.
    + intros b Hb. injection Hb as <-. cbn. lia.
Qed.

Lemma W_nil : forall l, W [] None 0%nat l.
Proof.
  intros l. split; [exact I|]. split.
  - intros op h Hop. destruct (open_nil _ _ Hop).
  - intros a Ha. discriminate.
Qed.

Lemma reachable_W : forall pol P E A k,
  holds W (iterate pol P E A no_outside_resumes k (initial P E)).
Proof.
  intros pol P E A k. apply reachable_holds;
    [apply W_closed | exact W_closed_turn | exact W_nil].
Qed.

(** ** S8: sleep commands and chains in range *)

(** Every sleep command so far is in range, and so is the awaited sleep's chain. *)
Definition C : Inv := fun tr aw _ _ =>
  (forall op h d, In (SleepCommand op h d) tr -> 0 < d <= max_chunk) /\
  (forall h op c r, aw = Some (AwaitSleep h op c r) -> chain_ok c r).

Lemma C_plain : forall tr aw aw' n n' l l' a,
  (forall op h d, a <> SleepCommand op h d) ->
  (forall h op c r, aw' = Some (AwaitSleep h op c r) -> aw = Some (AwaitSleep h op c r)) ->
  C tr aw n l -> C (tr ++ [a]) aw' n' l'.
Proof.
  intros tr aw aw' n n' l l' a Ha Haw [H1 H2]. split.
  - intros op h d Hin. destruct (in_snoc _ _ _ Hin) as [Hin'|Heq].
    + exact (H1 _ _ _ Hin').
    + destruct (Ha op h d). symmetry. exact Heq.
  - intros h op c r Hs. exact (H2 _ _ _ _ (Haw _ _ _ _ Hs)).
Qed.

Lemma C_new : forall tr aw n l n' l' op h c r,
  chain_ok c r -> C tr aw n l ->
  C (tr ++ [SleepCommand op h c]) (Some (AwaitSleep h op c r)) n' l'.
Proof.
  intros tr aw n l n' l' op h c r Hok [H1 H2]. split.
  - intros op' h' d Hin. destruct (in_snoc _ _ _ Hin) as [Hin'|Heq].
    + exact (H1 _ _ _ Hin').
    + inversion Heq; subst. exact (proj1 Hok).
  - intros h' op' c' r' Hs. inversion Hs; subst. exact Hok.
Qed.

Lemma C_closed : closed policy_v1 C.
Proof.
  split.
  - intros tr aw n l a [Hc _] H. apply C_plain with aw n l; [|auto|exact H].
    intros op h d ->. discriminate.
  - intros tr aw n l h H. apply C_plain with aw n l; [discriminate| |exact H].
    intros h' op c r Hs. apply cleared_some with h. exact Hs.
  - intros tr n l h k a H. apply C_plain with None n l; [discriminate| |exact H].
    intros h' op c r Hs. discriminate.
  - intros tr n l h c r Hok H. exact (C_new _ _ _ _ _ _ _ _ _ _ Hok H).
Qed.

Lemma C_link : forall r c' r', (forall d, r = Remaining d -> 0 < d) ->
  next_link r = Some (c', r') -> chain_ok c' r'.
Proof.
  intros r c' r' Hr Hn. unfold next_link in Hn. unfold chain_ok.
  destruct r as [|d|].
  - discriminate.
  - specialize (Hr d eq_refl).
    destruct (d <=? max_chunk) eqn:Hd; inversion Hn; subst; unfold max_chunk in *.
    + apply Z.leb_le in Hd. split; [lia | intros d' Hd'; discriminate].
    + apply Z.leb_gt in Hd. split; [lia|]. intros d' Hd'. injection Hd' as <-. lia.
  - inversion Hn; subst. unfold max_chunk. split; [lia | intros d' Hd'; discriminate].
Qed.

Lemma C_closed_turn : closed_turn C.
Proof.
  split.
  - intros tr aw n l i s floor _ H.
    apply C_plain with (Some aw) n l; [discriminate | auto |].
    apply C_plain with (Some aw) n l; [discriminate | auto | exact H].
  - intros tr aw n l o H. apply C_plain with (Some aw) n l; [discriminate| |exact H].
    intros h op c r Hs. discriminate.
  - intros tr h op c r n l c' r' Hn H. apply C_new with (Some (AwaitSleep h op c r)) n l;
      [|exact H].
    destruct H as [_ H2]. destruct (H2 _ _ _ _ eq_refl) as [_ Hr].
    exact (C_link _ _ _ Hr Hn).
Qed.

Lemma C_nil : forall l, C [] None 0%nat l.
Proof. intros l. split; [intros op h d Hin; destruct Hin | intros h op c r Hs; discriminate]. Qed.

Lemma reachable_C : forall P E A k,
  holds C (iterate policy_v1 P E A no_outside_resumes k (initial P E)).
Proof.
  intros P E A k. apply reachable_holds; [exact C_closed | exact C_closed_turn | exact C_nil].
Qed.

(** ** S8: [L] does not decrease *)

(** [C], and [L] at least [L0]. *)
Definition M (L0 : Z) : Inv := fun tr aw n l => C tr aw n l /\ L0 <= l.

Lemma M_closed : forall L0, closed policy_v1 (M L0).
Proof.
  intros L0. split.
  - intros tr aw n l a Ha [H Hl]. split; [apply (c_quiet _ _ C_closed); assumption | exact Hl].
  - intros tr aw n l h [H Hl]. split; [apply (c_interrupt _ _ C_closed); exact H | exact Hl].
  - intros tr n l h k a [H Hl]. split; [apply (c_command _ _ C_closed); exact H | exact Hl].
  - intros tr n l h c r Hs [H Hl].
    split; [apply (c_sleep _ _ C_closed); assumption | exact Hl].
Qed.

Lemma M_closed_turn : forall L0, closed_turn (M L0).
Proof.
  intros L0. split.
  - intros tr aw n l i s floor Hf [H Hl].
    split; [apply (c_sample _ C_closed_turn); assumption|].
    unfold next_logical. destruct Hf as [->|(h & op & r & ->)]; [lia|].
    destruct H as [_ H2]. destruct (H2 _ _ _ _ eq_refl) as [Hc _]. lia.
  - intros tr aw n l o [H Hl].
    split; [apply (c_deliver _ C_closed_turn); exact H | exact Hl].
  - intros tr h op c r n l c' r' Hn [H Hl].
    split; [eapply (c_link _ C_closed_turn); [exact Hn | exact H] | exact Hl].
Qed.

(** ** S5: no outside-resume violation outside the resume branch *)

Definition N : Inv := fun tr _ _ _ => ~ In (Violated StepOutsideTurn) tr.

Lemma N_snoc : forall tr a, a <> Violated StepOutsideTurn ->
  ~ In (Violated StepOutsideTurn) tr -> ~ In (Violated StepOutsideTurn) (tr ++ [a]).
Proof.
  intros tr a Ha H Hin. destruct (in_snoc _ _ _ Hin) as [Hin'|Heq].
  - exact (H Hin').
  - exact (Ha (eq_sym Heq)).
Qed.

Lemma N_closed : forall pol, closed pol N.
Proof.
  intros pol. split.
  - intros tr aw n l a [_ Ha] H. exact (N_snoc _ _ Ha H).
  - intros tr aw n l h H. apply N_snoc; [discriminate | exact H].
  - intros tr n l h k a H. apply N_snoc; [discriminate | exact H].
  - intros tr n l h c r _ H. apply N_snoc; [discriminate | exact H].
Qed.

Lemma N_closed_turn : closed_turn N.
Proof.
  split.
  - intros tr aw n l i s floor _ H. apply N_snoc; [discriminate|].
    apply N_snoc; [discriminate | exact H].
  - intros tr aw n l o H. apply N_snoc; [discriminate | exact H].
  - intros tr h op c r n l c' r' _ H. apply N_snoc; [discriminate | exact H].
Qed.
