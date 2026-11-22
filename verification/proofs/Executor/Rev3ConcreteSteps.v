(** * The invariant across the concrete runtime's single updates.

    Each lemma covers one kind of update [go], [interrupt] or a task makes: a fiber parks or
    blocks, starts an operation, exits, forks, registers, or a waiting fiber is woken.
    Proofs of the rev3 domain. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Concrete Rev3Monitor Rev3ConcreteBase.
Import ListNotations.
Open Scope nat_scope.

(** ** Monitor updates *)

Lemma rev3_pend_same : forall m e, (match e with LTask _ => False | LEvent (EvRelease _ _) => False
  | _ => True end) -> mpend (mnext m e) =
  match e with LEvent (EvStart f tok _) => [(f, tok)] | _ => [] end ++ mpend m.
Proof.
  intros m e Hk. simpl. f_equal. apply forallb_filter_id. apply forallb_forall.
  intros [g t] _. unfold still_open.
  destruct e as [|[]| | |]; try destruct Hk; reflexivity.
Qed.

(** ** Records and running fibers *)

Lemma rev3_pre_of_record : forall m s f p p',
  Inv m s -> look f s = Some p -> begun p = true -> status p <> Finished -> no_pend m f ->
  fid p' = f -> begun p' = true -> status p' = Ready -> Pre m s p'.
Proof.
  intros m s f p p' H Hl Hb Hf Hp Hid Hb' Hr. constructor; rewrite ?Hid.
  - exact (i_begun _ _ H _ _ Hl Hb).
  - intros h Hh. rewrite Hl in Hh. injection Hh as <-. exact Hf.
  - exact Hp.
  - exact (i_fid _ _ H _ _ Hl).
  - exact Hb'.
  - exact Hr.
Qed.

Lemma rev3_no_pend_record : forall m s f p,
  Inv m s -> look f s = Some p -> (forall tok, status p <> Await tok) -> no_pend m f.
Proof.
  intros m s f p H Hl Hn tok Hin. destruct (i_pend _ _ H _ _ Hin) as [h [Hh Hs]].
  rewrite Hl in Hh. injection Hh as <-. exact (Hn tok Hs).
Qed.

Lemma rev3_begun_record : forall m s f p,
  Inv m s -> look f s = Some p -> status p <> Ready -> begun p = true.
Proof.
  intros m s f p H Hl Hn. destruct (begun p) eqn:E; [reflexivity|].
  exfalso. apply Hn. exact (proj2 (i_fresh _ _ H _ _ Hl E)).
Qed.

(** A ready record of a started fiber is a fiber that may run. *)
Lemma rev3_pre_ready : forall m s f p,
  Inv m s -> look f s = Some p -> status p = Ready -> In f (mreg m) -> Pre m s p.
Proof.
  intros m s f p H Hl Hr Hreg. destruct (rev3_look_some _ _ _ Hl) as [Hid _].
  assert (Hb : begun p = true).
  { destruct (begun p) eqn:E; [reflexivity|]. exfalso.
    exact (proj1 (i_fresh _ _ H _ _ Hl E) Hreg). }
  apply (rev3_pre_of_record m s f p p H Hl Hb); [congruence| |exact Hid|exact Hb|exact Hr].
  apply (rev3_no_pend_record m s f p H Hl). congruence.
Qed.

(** ** Posts for the updates of a running fiber *)

Lemma rev3_post_put_running : forall m s g g',
  Inv m s -> Pre m s g -> fid g' = fid g -> begun g' = true ->
  status g' <> Finished -> (forall tok, status g' <> Await tok) ->
  Post m s (Some (fid g)) m (put g' s).
Proof.
  intros m s g g' H P Hid Hb Hf Ha. split; [exact (rev3_inv_put_running m s g g' H P Hid Hb Hf Ha)|].
  split; [rewrite <- Hid; apply rev3_ext_put|intros x Hx; exact Hx].
Qed.

Lemma rev3_pre_put_self : forall m s g g',
  Pre m s g -> fid g' = fid g -> status g' <> Finished -> Pre m (put g' s) g.
Proof.
  intros m s g g' P Hid Hf. destruct P as [p_reg0 p_live0 p_pend0 p_fid0 p_begun0 p_ready0]. constructor; auto.
  intros h Hh. rewrite <- Hid in Hh. rewrite rev3_look_put_eq in Hh. injection Hh as <-. exact Hf.
Qed.

(** A running fiber parks itself on the queue. *)
Lemma rev3_post_park : forall m s g g' p,
  Inv m s -> Pre m s g -> fid g' = fid g -> begun g' = true -> status g' = Ready ->
  wp m (Concrete.enqueue (put g' s) g' p) (Post m s (Some (fid g))).
Proof.
  intros m s g g' p H P Hid Hb Hr.
  assert (Hnf : status g' <> Finished) by congruence.
  assert (Hna : forall tok, status g' <> Await tok) by congruence.
  pose proof (rev3_post_put_running m s g g' H P Hid Hb Hnf Hna) as Post1.
  apply rev3_wp_enqueue; intros _; [exact Post1|].
  destruct Post1 as [H1 [E1 I1]].
  pose proof (rev3_pre_put_self m s g g' P Hid Hnf) as P1.
  destruct (rev3_set_queued_fields g' true) as [F1 [F2 F3]].
  pose proof (rev3_post_put_running m (put g' s) g (set_queued g' true) H1 P1
    ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence)) as Post2.
  exact (rev3_post_trans _ _ _ _ _ _ _ E1 I1 Post2).
Qed.

(** ** Fresh identities and tokens *)

Lemma rev3_look_bump_fid : forall s f, look f (bump_fid s) = look f s.
Proof. reflexivity. Qed.

Lemma rev3_look_bump_tok : forall s f, look f (bump_tok s) = look f s.
Proof. reflexivity. Qed.

Lemma rev3_look_set_cell : forall s c v f, look f (set_cell s c v) = look f s.
Proof. reflexivity. Qed.

Lemma rev3_ext_same_fibers : forall s s',
  fibers s' = fibers s -> next_fid s <= next_fid s' -> Ext s None s'.
Proof.
  intros s s' Hf Hn. split; [exact Hn|split].
  - intros f h Hl. exists h. unfold Concrete.find in *. rewrite Hf. exact Hl.
  - intros f h _ Hl Hr. exists h. unfold Concrete.find in *. rewrite Hf. split; assumption.
Qed.

Lemma rev3_inv_same_fibers : forall m s s',
  Inv m s -> fibers s' = fibers s -> next_fid s <= next_fid s' -> next_tok s <= next_tok s' ->
  (next_fid s' = next_fid s \/ mfirst m = Some 0) -> Inv m s'.
Proof.
  intros m s s' H Hf Hn Ht Hnf.
  assert (Hl : forall f, look f s' = look f s) by (intros f; unfold Concrete.find; rewrite Hf;
    reflexivity).
  destruct H as [i_nodup0 i_fid0 i_reg0 i_begun0 i_fresh0 i_ex0 i_pend0 i_toks0 i_rx0 i_pos0 i_root0 i_first0]. constructor; try (intros; rewrite ?Hl in *; eauto; fail).
  - rewrite Hf. assumption.
  - intros f h Hh. rewrite Hl in Hh. specialize (i_fid0 _ _ Hh). lia.
  - intros f Hin. specialize (i_reg0 _ Hin). lia.
  - intros tok Hin. specialize (i_toks0 _ Hin). lia.
  - lia.
  - destruct Hnf as [E|E]; [rewrite E; exact i_first0|left; exact E].
Qed.

Lemma rev3_pre_same_fibers : forall m s s' g,
  Pre m s g -> fibers s' = fibers s -> next_fid s <= next_fid s' -> Pre m s' g.
Proof.
  intros m s s' g P Hf Hn.
  assert (Hl : forall f, look f s' = look f s) by (intros f; unfold Concrete.find; rewrite Hf;
    reflexivity).
  destruct P as [p_reg0 p_live0 p_pend0 p_fid0 p_begun0 p_ready0]. constructor; auto.
  - intros h Hh. rewrite Hl in Hh. eauto.
  - lia.
Qed.

Lemma rev3_look_fresh : forall m s, Inv m s -> look (next_fid s) s = None.
Proof.
  intros m s H. destruct (look (next_fid s) s) eqn:E; [|reflexivity].
  pose proof (i_fid _ _ H _ _ E). lia.
Qed.

(** A durable operation starts: a new token, an open await, the record awaits it. *)
Lemma rev3_post_start : forall m s g op k,
  Inv m s -> Pre m s g ->
  mok m (LEvent (EvStart (fid g) (next_tok s) op)) /\
  Post m s (Some (fid g)) (mnext m (LEvent (EvStart (fid g) (next_tok s) op)))
    (put (with_konts (with_code g (CEnd 0) (Await (next_tok s))) k dummy_nat) (bump_tok s)).
Proof.
  intros m s g op k H P.
  set (tok := next_tok s). set (g' := with_konts (with_code g (CEnd 0) (Await tok)) k dummy_nat).
  set (m' := mnext m (LEvent (EvStart (fid g) tok op))).
  assert (Hpend : mpend m' = (fid g, tok) :: mpend m)
    by (apply (rev3_pend_same m (LEvent (EvStart (fid g) tok op))); exact I).
  split.
  { apply rev3_mok_start; [exact (p_reg _ _ _ P)|exact (rev3_not_exited _ _ _ H P)|
      exact (p_pend _ _ _ P)|]. intros Hin. pose proof (i_toks _ _ H _ Hin). unfold tok in *. lia. }
  assert (Hlook : forall f, look f (put g' (bump_tok s)) =
            if f =? fid g then Some g' else look f s)
    by (intros f; rewrite rev3_look_put; reflexivity).
  split; [|split].
  - destruct H as [i_nodup0 i_fid0 i_reg0 i_begun0 i_fresh0 i_ex0 i_pend0 i_toks0 i_rx0 i_pos0 i_root0 i_first0].
  destruct P as [p_reg0 p_live0 p_pend0 p_fid0 p_begun0 p_ready0]. constructor.
    + apply rev3_nodup_put. assumption.
    + intros f h Hh. rewrite Hlook in Hh. simpl. destruct (f =? fid g) eqn:E; [|eauto].
      apply Nat.eqb_eq in E. subst. assumption.
    + simpl. assumption.
    + intros f h Hh Hb. rewrite Hlook in Hh. simpl. destruct (f =? fid g) eqn:E; [|eauto].
      apply Nat.eqb_eq in E. subst. assumption.
    + intros f h Hh Hb. rewrite Hlook in Hh. simpl. destruct (f =? fid g) eqn:E; [|eauto].
      injection Hh as <-. simpl in Hb. congruence.
    + intros f Hin. rewrite Hlook. simpl in Hin. destruct (f =? fid g) eqn:E; [|eauto].
      apply Nat.eqb_eq in E. subst. exfalso.
      destruct (i_ex0 _ Hin) as [h [Hh Hs]]. exact (p_live0 h Hh Hs).
    + intros f t Hin. rewrite Hpend in Hin. rewrite Hlook.
      destruct Hin as [Heq|Hin].
      * injection Heq as <- <-. rewrite Nat.eqb_refl. exists g'. split; reflexivity.
      * destruct (f =? fid g) eqn:E; [|eauto].
        apply Nat.eqb_eq in E. subst. destruct (p_pend0 t Hin).
    + intros t Hin. simpl in Hin |- *. destruct Hin as [<-|Hin]; [unfold tok; lia|].
      specialize (i_toks0 _ Hin). lia.
    + simpl. assumption.
    + simpl. assumption.
    + intros H0. rewrite Hlook. destruct (0 =? fid g); [discriminate|]. auto.
    + unfold m'. rewrite rev3_mfirst_other by exact I. simpl. exact i_first0.
  - apply (rev3_ext_trans _ (bump_tok s)).
    + apply rev3_ext_none. apply rev3_ext_same_fibers; reflexivity.
    + change (fid g) with (fid g'). apply rev3_ext_put.
  - intros x Hx. exact Hx.
Qed.

(** A fiber exits: it is recorded exited, and for the root the root exit is recorded. *)
Lemma rev3_inv_exit : forall m m' s g c,
  Inv m s -> Pre m s g ->
  mreg m' = mreg m -> mex m' = fid g :: mex m -> incl (mpend m') (mpend m) ->
  mtoks m' = mtoks m -> (mrx m' = true -> mrx m = true \/ fid g = 0) ->
  mfirst m' = mfirst m -> Inv m' (put (with_code g c Finished) s).
Proof.
  intros m m' s g c H P Hr He Hp Ht Hx Hf.
  set (g' := with_code g c Finished).
  assert (Hlook : forall f, look f (put g' s) = if f =? fid g then Some g' else look f s)
    by (intros f; rewrite rev3_look_put; reflexivity).
  pose proof (rev3_not_exited _ _ _ H P) as Hne.
  destruct H as [i_nodup0 i_fid0 i_reg0 i_begun0 i_fresh0 i_ex0 i_pend0 i_toks0 i_rx0 i_pos0 i_root0 i_first0].
  destruct P as [p_reg0 p_live0 p_pend0 p_fid0 p_begun0 p_ready0]. constructor; rewrite ?Hr, ?He, ?Ht.
  - apply rev3_nodup_put. assumption.
  - intros f h Hh. rewrite Hlook in Hh. simpl. destruct (f =? fid g) eqn:E; [|eauto].
    apply Nat.eqb_eq in E. subst. assumption.
  - simpl. assumption.
  - intros f h Hh Hb. rewrite Hlook in Hh. destruct (f =? fid g) eqn:E; [|eauto].
    apply Nat.eqb_eq in E. subst. assumption.
  - intros f h Hh Hb. rewrite Hlook in Hh. destruct (f =? fid g) eqn:E; [|eauto].
    injection Hh as <-. simpl in Hb. congruence.
  - intros f [<-|Hin]; rewrite Hlook.
    + rewrite Nat.eqb_refl. exists g'. split; reflexivity.
    + destruct (f =? fid g) eqn:E; [|eauto].
      apply Nat.eqb_eq in E. subst. contradiction.
  - intros f t Hin. apply Hp in Hin. rewrite Hlook. destruct (f =? fid g) eqn:E; [|eauto].
    apply Nat.eqb_eq in E. subst. destruct (p_pend0 t Hin).
  - simpl. assumption.
  - intros Hx'. destruct (Hx Hx') as [Hx''|H0]; [right; auto|left; exact H0].
  - simpl. assumption.
  - intros H0. rewrite Hlook. destruct (0 =? fid g); [discriminate|]. auto.
  - rewrite Hf. exact i_first0.
Qed.

(** ** Waking waiting fibers *)

Lemma rev3_wake_ok : forall gs s m pick,
  Inv m s -> NoDup (map fid gs) -> (forall g, In g gs -> look (fid g) s = Some g) ->
  (forall g c, In g gs -> pick g = Some c ->
     status g <> Finished /\ forall tok, status g <> Await tok) ->
  wp m (wake s gs pick) (fun m' s' => m' = m /\ Inv m s' /\ Ext s None s').
Proof.
  induction gs as [|g gs IH]; intros s m pick H Hnd Hin Hpick; simpl.
  - split; [reflexivity|split; [exact H|apply rev3_ext_refl]].
  - inversion Hnd as [|x y Hnot Hnd']; subst.
    assert (Hrest : forall g', In g' gs -> look (fid g') s = Some g')
      by (intros g' Hg'; apply Hin; right; exact Hg').
    assert (Hpick' : forall g' c, In g' gs -> pick g' = Some c ->
              status g' <> Finished /\ forall tok, status g' <> Await tok)
      by (intros g' c Hg'; apply Hpick; right; exact Hg').
    destruct (pick g) as [c|] eqn:Ep; [|exact (IH s m pick H Hnd' Hrest Hpick')].
    destruct (Hpick g c (or_introl eq_refl) Ep) as [Hnf Hna].
    pose proof (Hin g (or_introl eq_refl)) as Hg.
    apply rev3_wp_sbind. apply rev3_wp_enqueue; intros Hq.
    + exact (IH s m pick H Hnd' Hrest Hpick').
    + set (g' := set_queued (with_code g c Ready) true).
      assert (Hinv : Inv m (put g' s)).
      { apply rev3_inv_put; [exact H|exact (i_fid _ _ H _ _ Hg)|..]; simpl.
        - exact (i_begun _ _ H _ _ Hg).
        - intros Hb. split; [exact (proj1 (i_fresh _ _ H _ _ Hg Hb))|reflexivity].
        - intros Hex. destruct (i_ex _ _ H _ Hex) as [h [Hh Hs]].
          rewrite Hg in Hh. injection Hh as <-. contradiction.
        - intros tok Hp. destruct (i_pend _ _ H _ _ Hp) as [h [Hh Hs]].
          rewrite Hg in Hh. injection Hh as <-. exfalso. exact (Hna tok Hs). }
      assert (Hrest' : forall g'', In g'' gs -> look (fid g'') (put g' s) = Some g'').
      { intros g'' Hg''. rewrite rev3_look_put_neq; [exact (Hrest g'' Hg'')|].
        simpl. intro E. apply Hnot. rewrite <- E. apply in_map. exact Hg''. }
      refine (rev3_wp_mono _ _ _ _ _ _ (IH (put g' s) m pick Hinv Hnd' Hrest' Hpick')).
      intros m' s' [-> [Hi He]]. split; [reflexivity|split; [exact Hi|]].
      apply (rev3_ext_trans _ (put g' s)); [|exact He].
      apply rev3_ext_put_ready. intros. reflexivity.
Qed.

Lemma rev3_wake_cell_ok : forall s m c v,
  Inv m s -> wp m (wake_cell s c v) (fun m' s' => m' = m /\ Inv m s' /\ Ext s None s').
Proof.
  intros s m c v H. unfold wake_cell. apply rev3_wake_ok; [exact H|exact (i_nodup _ _ H)| |].
  - intros g Hg. apply rev3_look_in; [exact (i_nodup _ _ H)|exact Hg].
  - intros g k _ Hp. destruct (status g); try discriminate; split; discriminate.
Qed.

Lemma rev3_wake_exit_ok : forall s m f,
  Inv m s -> wp m (wake_exit s f) (fun m' s' => m' = m /\ Inv m s' /\ Ext s None s').
Proof.
  intros s m f H. unfold wake_exit. apply rev3_wake_ok; [exact H|exact (i_nodup _ _ H)| |].
  - intros g Hg. apply rev3_look_in; [exact (i_nodup _ _ H)|exact Hg].
  - intros g k _ Hp. destruct (status g); try discriminate; split; discriminate.
Qed.

(** ** Registering a fiber *)

(** A fresh identity is registered and allocated. *)
Lemma rev3_inv_register_fresh : forall m s b,
  Inv m s -> mfirst m = Some 0 -> Inv (mnext m (LRegister (next_fid s) b)) (bump_fid s).
Proof.
  intros m s b H Hf0.
  assert (Hp : mpend (mnext m (LRegister (next_fid s) b)) = mpend m)
    by (apply (rev3_pend_same m (LRegister (next_fid s) b)); exact I).
  destruct H as [i_nodup0 i_fid0 i_reg0 i_begun0 i_fresh0 i_ex0 i_pend0 i_toks0 i_rx0 i_pos0
    i_root0 i_first0].
  constructor; rewrite ?Hp; cbn [mnext mreg mex mtoks mrx bump_fid next_fid next_tok fibers].
  - exact i_nodup0.
  - intros f h Hh. specialize (i_fid0 _ _ Hh). lia.
  - intros f [<-|Hin]; [lia|]. specialize (i_reg0 _ Hin). lia.
  - intros f h Hh Hb. right. eauto.
  - intros f h Hh Hb. destruct (i_fresh0 _ _ Hh Hb) as [Hn Hr]. split; [|exact Hr].
    intros [E|Hin]; [|contradiction]. specialize (i_fid0 _ _ Hh). lia.
  - exact i_ex0.
  - exact i_pend0.
  - exact i_toks0.
  - exact i_rx0.
  - lia.
  - intros [E|Hin]; [lia|]. auto.
  - left. simpl. rewrite Hf0. reflexivity.
Qed.

Lemma rev3_pre_register_fresh : forall m s g b,
  Inv m s -> Pre m s g -> Pre (mnext m (LRegister (next_fid s) b)) (bump_fid s) g.
Proof.
  intros m s g b H P.
  assert (Hp : mpend (mnext m (LRegister (next_fid s) b)) = mpend m)
    by (apply (rev3_pend_same m (LRegister (next_fid s) b)); exact I).
  destruct P as [p_reg0 p_live0 p_pend0 p_fid0 p_begun0 p_ready0].
  constructor; cbn [mnext mreg bump_fid next_fid fibers].
  - right. exact p_reg0.
  - exact p_live0.
  - intros tok Hin. unfold no_pend in *. rewrite Hp in Hin. exact (p_pend0 tok Hin).
  - lia.
  - exact p_begun0.
  - exact p_ready0.
Qed.

(** A begun record is registered: the record's fiber was not started before. *)
Lemma rev3_inv_register_record : forall m s f h g' b,
  Inv m s -> look f s = Some h -> begun h = false -> fid g' = f -> begun g' = true ->
  status g' = Ready -> Inv (mnext m (LRegister f b)) (put g' s).
Proof.
  intros m s f h g' b H Hl Hb Hid Hb' Hr. subst f.
  assert (Hp : mpend (mnext m (LRegister (fid g') b)) = mpend m)
    by (apply (rev3_pend_same m (LRegister (fid g') b)); exact I).
  assert (Hlook : forall x, look x (put g' s) = if x =? fid g' then Some g' else look x s)
    by (intros x; rewrite rev3_look_put; reflexivity).
  pose proof (i_fresh _ _ H _ _ Hl Hb) as [Hnr Hrd].
  destruct H as [i_nodup0 i_fid0 i_reg0 i_begun0 i_fresh0 i_ex0 i_pend0 i_toks0 i_rx0 i_pos0
    i_root0 i_first0].
  constructor; rewrite ?Hp; cbn [mnext mreg mex mtoks mrx].
  - apply rev3_nodup_put. assumption.
  - intros x y Hy. rewrite Hlook in Hy. simpl. destruct (x =? fid g') eqn:E; [|eauto].
    apply Nat.eqb_eq in E. subst. eauto.
  - intros x [<-|Hin]; simpl; eauto.
  - intros x y Hy Hb''. rewrite Hlook in Hy. destruct (x =? fid g') eqn:E.
    + apply Nat.eqb_eq in E. left. symmetry. exact E.
    + right. eauto.
  - intros x y Hy Hb''. rewrite Hlook in Hy. destruct (x =? fid g') eqn:E.
    + injection Hy as <-. congruence.
    + destruct (i_fresh0 _ _ Hy Hb'') as [Hn Hr']. split; [|exact Hr'].
      intros [E'|Hin]; [|contradiction]. subst. rewrite Nat.eqb_refl in E. discriminate.
  - intros x Hin. rewrite Hlook. destruct (x =? fid g') eqn:E; [|eauto].
    apply Nat.eqb_eq in E. subst. destruct (i_ex0 _ Hin) as [y [Hy Hs]].
    rewrite Hl in Hy. injection Hy as <-. congruence.
  - intros x t Hin. rewrite Hlook. destruct (x =? fid g') eqn:E; [|eauto].
    apply Nat.eqb_eq in E. subst. destruct (i_pend0 _ _ Hin) as [y [Hy Hs]].
    rewrite Hl in Hy. injection Hy as <-. congruence.
  - assumption.
  - assumption.
  - assumption.
  - intros H0. rewrite Hlook. destruct (0 =? fid g') eqn:E; [discriminate|].
    destruct H0 as [E'|H0]; [rewrite E' in E; rewrite Nat.eqb_refl in E; discriminate|auto].
  - left. simpl. destruct i_first0 as [E|[E [_ E1]]]; rewrite E; [reflexivity|].
    pose proof (i_fid0 _ _ Hl). f_equal. lia.
Qed.

Lemma rev3_mok_register_record : forall m s f h b,
  Inv m s -> look f s = Some h -> begun h = false -> mok m (LRegister f b).
Proof.
  intros m s f h b H Hl Hb. destruct (i_fresh _ _ H _ _ Hl Hb) as [Hn Hr].
  apply rev3_mok_register; [exact Hn| |].
  - intros Hin. destruct (i_ex _ _ H _ Hin) as [y [Hy Hs]]. rewrite Hl in Hy.
    injection Hy as <-. congruence.
  - apply (rev3_no_pend_record m s f h H Hl). congruence.
Qed.

Lemma rev3_mok_register_fresh : forall m s b,
  Inv m s -> mok m (LRegister (next_fid s) b).
Proof.
  intros m s b H. pose proof (rev3_look_fresh m s H) as Hn.
  apply rev3_mok_register.
  - intros Hin. pose proof (i_reg _ _ H _ Hin). lia.
  - intros Hin. destruct (i_ex _ _ H _ Hin) as [y [Hy _]]. congruence.
  - intros tok Hin. destruct (i_pend _ _ H _ _ Hin) as [y [Hy _]]. congruence.
Qed.
