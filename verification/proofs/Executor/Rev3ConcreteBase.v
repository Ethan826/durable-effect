(** * The concrete runtime's state: lookups, updates and the invariant for [MeetsConcrete].

    [Inv m s] ties the monitor state [m] of Rev3Monitor.v to the concrete state [s]: every
    started fiber has an identity below [next_fid], a fiber is started exactly when its record
    says it has begun, an exited fiber's record is finished, an open await's record awaits
    its token, and every started token is below [next_tok]. Proofs of the rev3 domain. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Concrete Rev3Monitor.
Import ListNotations.
Open Scope nat_scope.

Notation look := Concrete.find.

(** ** Lookups after an update *)

Lemma rev3_look_some : forall f s h, look f s = Some h -> fid h = f /\ In h (fibers s).
Proof.
  intros f s h H. unfold Concrete.find in H. apply find_some in H. destruct H as [Hin He].
  apply Nat.eqb_eq in He. split; assumption.
Qed.

Lemma rev3_look_none : forall f s, look f s = None -> forall h, In h (fibers s) -> fid h <> f.
Proof.
  intros f s H h Hin. unfold Concrete.find in H. pose proof (find_none _ _ H h Hin) as E.
  apply Nat.eqb_neq in E. exact E.
Qed.

Lemma rev3_find_map_eq : forall (g : Fiber) l,
  existsb (fun h => fid h =? fid g) l = true ->
  List.find (fun h => fid h =? fid g)
    (map (fun h => if fid h =? fid g then g else h) l) = Some g.
Proof.
  intros g l. induction l as [|h l IH]; simpl; [discriminate|].
  destruct (fid h =? fid g) eqn:E; simpl.
  - rewrite Nat.eqb_refl. reflexivity.
  - rewrite E. exact IH.
Qed.

Lemma rev3_find_map_neq : forall (g : Fiber) f l, f <> fid g ->
  List.find (fun h => fid h =? f) (map (fun h => if fid h =? fid g then g else h) l) =
  List.find (fun h => fid h =? f) l.
Proof.
  intros g f l Hne. induction l as [|h l IH]; simpl; [reflexivity|].
  destruct (fid h =? fid g) eqn:E; simpl.
  - apply Nat.eqb_eq in E. assert (Hf : fid g =? f = false) by (apply Nat.eqb_neq; lia).
    assert (Hh : fid h =? f = false) by (apply Nat.eqb_neq; lia).
    rewrite Hf, Hh. exact IH.
  - destruct (fid h =? f); [reflexivity|exact IH].
Qed.

Lemma rev3_find_app_none : forall (p : Fiber -> bool) l x,
  List.find p l = None -> List.find p (l ++ [x]) = if p x then Some x else None.
Proof.
  intros p l x. induction l as [|h l IH]; simpl; [reflexivity|].
  destruct (p h); [discriminate|exact IH].
Qed.

Lemma rev3_find_app_some : forall (p : Fiber -> bool) l x y,
  List.find p l = Some y -> List.find p (l ++ [x]) = Some y.
Proof.
  intros p l x y. induction l as [|h l IH]; simpl; [discriminate|].
  destruct (p h); [exact (fun H => H)|exact IH].
Qed.

Lemma rev3_look_put_eq : forall g s, look (fid g) (put g s) = Some g.
Proof.
  intros g s. unfold Concrete.find, put. simpl.
  destruct (existsb (fun h => fid h =? fid g) (fibers s)) eqn:E.
  - apply rev3_find_map_eq. exact E.
  - rewrite rev3_find_app_none; [rewrite Nat.eqb_refl; reflexivity|].
    destruct (List.find (fun h => fid h =? fid g) (fibers s)) eqn:F; [|reflexivity].
    apply find_some in F. destruct F as [Hin Hp].
    assert (existsb (fun h => fid h =? fid g) (fibers s) = true)
      by (apply existsb_exists; exists f; split; assumption).
    congruence.
Qed.

Lemma rev3_look_put_neq : forall g s f, f <> fid g -> look f (put g s) = look f s.
Proof.
  intros g s f Hne. unfold Concrete.find, put. simpl.
  destruct (existsb (fun h => fid h =? fid g) (fibers s)).
  - apply rev3_find_map_neq. exact Hne.
  - destruct (List.find (fun h => fid h =? f) (fibers s)) eqn:F.
    + apply rev3_find_app_some. exact F.
    + rewrite rev3_find_app_none by exact F.
      assert (Hf : fid g =? f = false) by (apply Nat.eqb_neq; lia). rewrite Hf. reflexivity.
Qed.

Lemma rev3_look_put : forall g s f,
  look f (put g s) = if f =? fid g then Some g else look f s.
Proof.
  intros g s f. destruct (f =? fid g) eqn:E.
  - apply Nat.eqb_eq in E. subst. apply rev3_look_put_eq.
  - apply Nat.eqb_neq in E. apply rev3_look_put_neq. exact E.
Qed.

Lemma rev3_put_fields : forall g s,
  program (put g s) = program s /\ cells (put g s) = cells s /\
  next_fid (put g s) = next_fid s /\ next_tok (put g s) = next_tok s.
Proof. intros. repeat split. Qed.

Lemma rev3_map_fid_replace : forall (g : Fiber) l,
  map fid (map (fun h => if fid h =? fid g then g else h) l) = map fid l.
Proof.
  intros g l. induction l as [|h l IH]; simpl; [reflexivity|].
  rewrite IH. destruct (fid h =? fid g) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E. rewrite E. reflexivity.
Qed.

Lemma rev3_nodup_put : forall g s, NoDup (map fid (fibers s)) -> NoDup (map fid (fibers (put g s))).
Proof.
  intros g s H. unfold put. simpl.
  destruct (existsb (fun h => fid h =? fid g) (fibers s)) eqn:E.
  - rewrite rev3_map_fid_replace. exact H.
  - rewrite map_app. simpl. apply NoDup_app; [exact H|constructor; [intros []|constructor]|].
    intros x Hx [<-|[]]. apply in_map_iff in Hx. destruct Hx as [h [Hh Hin]].
    assert (existsb (fun h => fid h =? fid g) (fibers s) = true).
    { apply existsb_exists. exists h. split; [exact Hin|]. apply Nat.eqb_eq. exact Hh. }
    congruence.
Qed.

Lemma rev3_look_in : forall l (g : Fiber), NoDup (map fid l) -> In g l ->
  List.find (fun h => fid h =? fid g) l = Some g.
Proof.
  induction l as [|h l IH]; intros g Hnd Hin; [destruct Hin|].
  simpl in Hnd. inversion Hnd as [|x y Hnot Hnd']; subst. simpl.
  destruct Hin as [<-|Hin]; [rewrite Nat.eqb_refl; reflexivity|].
  destruct (fid h =? fid g) eqn:E.
  - apply Nat.eqb_eq in E. exfalso. apply Hnot. rewrite E. apply in_map. exact Hin.
  - apply IH; assumption.
Qed.

(** ** Field facts about the fiber updates *)

Lemma rev3_with_code_fields : forall g c st,
  fid (with_code g c st) = fid g /\ begun (with_code g c st) = begun g /\
  status (with_code g c st) = st /\ queued (with_code g c st) = queued g.
Proof. intros. repeat split. Qed.

Lemma rev3_with_flags_fields : forall g m i u q b e,
  fid (with_flags g m i u q b e) = fid g /\ begun (with_flags g m i u q b e) = b /\
  status (with_flags g m i u q b e) = status g.
Proof. intros. repeat split. Qed.

Lemma rev3_unwind_fields : forall g e,
  fid (unwind g e) = fid g /\ begun (unwind g e) = begun g /\ status (unwind g e) = Ready.
Proof. intros g e. unfold unwind. destruct (unwinding g); repeat split. Qed.

Lemma rev3_konts_fields : forall g ko kn,
  fid (with_konts g ko kn) = fid g /\ begun (with_konts g ko kn) = begun g /\
  status (with_konts g ko kn) = status g.
Proof. intros. repeat split. Qed.

(** ** The invariant *)

Record Inv (m : Mon) (s : CState) : Prop := {
  i_nodup : NoDup (map fid (fibers s));
  i_fid : forall f h, look f s = Some h -> f < next_fid s;
  i_reg : forall f, In f (mreg m) -> f < next_fid s;
  i_begun : forall f h, look f s = Some h -> begun h = true -> In f (mreg m);
  i_fresh : forall f h, look f s = Some h -> begun h = false ->
              ~ In f (mreg m) /\ status h = Ready;
  i_ex : forall f, In f (mex m) -> exists h, look f s = Some h /\ status h = Finished;
  i_pend : forall f tok, In (f, tok) (mpend m) ->
             exists h, look f s = Some h /\ status h = Await tok;
  i_toks : forall tok, In tok (mtoks m) -> tok < next_tok s;
  i_rx : mrx m = true -> In 0 (mex m);
  i_pos : 0 < next_fid s;
  i_root : In 0 (mreg m) -> look 0 s <> None;
  i_first : mfirst m = Some 0 \/ (mfirst m = None /\ mreg m = [] /\ next_fid s = 1)
}.

(** Once any fiber has started, the first one started is the root. *)
Lemma rev3_first_root : forall m s f, Inv m s -> In f (mreg m) -> mfirst m = Some 0.
Proof.
  intros m s f H Hin. destruct (i_first _ _ H) as [E|[_ [E _]]]; [exact E|].
  rewrite E in Hin. destruct Hin.
Qed.

(** Entries other than a register leave the first fiber started as it was. *)
Lemma rev3_mfirst_other : forall m e,
  (match e with LRegister _ _ => False | _ => True end) -> mfirst (mnext m e) = mfirst m.
Proof.
  intros m e Hk. simpl. destruct (mfirst m); [reflexivity|]. destruct e; try destruct Hk;
  reflexivity.
Qed.

(** A fiber is running and may act: it has started, it has not exited, and it has no open
    await. *)
Record Pre (m : Mon) (s : CState) (g : Fiber) : Prop := {
  p_reg : In (fid g) (mreg m);
  p_live : forall h, look (fid g) s = Some h -> status h <> Finished;
  p_pend : no_pend m (fid g);
  p_fid : fid g < next_fid s;
  p_begun : begun g = true;
  p_ready : status g = Ready
}.

(** What a script keeps of the state it started from: identities are not reused, records are
    not removed, and a ready record of any fiber but the one running stays ready. *)
Definition Ext (s0 : CState) (who : option FiberId) (s1 : CState) : Prop :=
  next_fid s0 <= next_fid s1 /\
  (forall f h, look f s0 = Some h -> exists h', look f s1 = Some h') /\
  (forall f h, who <> Some f -> look f s0 = Some h -> status h = Ready ->
     exists h', look f s1 = Some h' /\ status h' = Ready).

Definition Post (m0 : Mon) (s0 : CState) (who : option FiberId) (m1 : Mon) (s1 : CState)
    : Prop :=
  Inv m1 s1 /\ Ext s0 who s1 /\ incl (mreg m0) (mreg m1).

Lemma rev3_ext_refl : forall s w, Ext s w s.
Proof.
  intros s w. split; [lia|split].
  - intros f h H. exists h. exact H.
  - intros f h _ H Hr. exists h. split; assumption.
Qed.

Lemma rev3_ext_trans : forall s0 s1 s2 w, Ext s0 w s1 -> Ext s1 w s2 -> Ext s0 w s2.
Proof.
  intros s0 s1 s2 w [A1 [B1 C1]] [A2 [B2 C2]]. split; [lia|split].
  - intros f h H. destruct (B1 _ _ H) as [h1 H1]. exact (B2 _ _ H1).
  - intros f h Hw H Hr. destruct (C1 _ _ Hw H Hr) as [h1 [H1 Hr1]]. exact (C2 _ _ Hw H1 Hr1).
Qed.

Lemma rev3_ext_none : forall s0 s1 w, Ext s0 None s1 -> Ext s0 w s1.
Proof.
  intros s0 s1 w [A [B C]]. split; [exact A|split; [exact B|]].
  intros f h _ H Hr. exact (C f h ltac:(discriminate) H Hr).
Qed.

Lemma rev3_ext_put : forall g s, Ext s (Some (fid g)) (put g s).
Proof.
  intros g s. split; [simpl; lia|split].
  - intros f h H. rewrite rev3_look_put. destruct (f =? fid g); [eexists; reflexivity|].
    exists h. exact H.
  - intros f h Hw H Hr. rewrite rev3_look_put_neq by (intro E; apply Hw; rewrite E; reflexivity).
    exists h. split; assumption.
Qed.

(** A put that keeps a ready record ready. *)
Lemma rev3_ext_put_ready : forall g s,
  (forall h, look (fid g) s = Some h -> status h = Ready -> status g = Ready) ->
  Ext s None (put g s).
Proof.
  intros g s Hg. split; [simpl; lia|split].
  - intros f h H. rewrite rev3_look_put. destruct (f =? fid g); [eexists; reflexivity|].
    exists h. exact H.
  - intros f h _ H Hr. rewrite rev3_look_put. destruct (f =? fid g) eqn:E.
    + apply Nat.eqb_eq in E. subst. exists g. split; [reflexivity|]. exact (Hg h H Hr).
    + exists h. split; assumption.
Qed.

Lemma rev3_post_trans : forall m0 s0 m1 s1 m2 s2 w,
  Ext s0 w s1 -> incl (mreg m0) (mreg m1) -> Post m1 s1 w m2 s2 -> Post m0 s0 w m2 s2.
Proof.
  intros m0 s0 m1 s1 m2 s2 w He Hi [Hinv [He' Hi']]. split; [exact Hinv|split].
  - exact (rev3_ext_trans _ _ _ _ He He').
  - intros x Hx. apply Hi'. apply Hi. exact Hx.
Qed.

Lemma rev3_post_weaken : forall m0 s0 m1 s1 w,
  Post m0 s0 None m1 s1 -> Post m0 s0 w m1 s1.
Proof.
  intros m0 s0 m1 s1 w [Hinv [He Hi]]. split; [exact Hinv|split; [|exact Hi]].
  apply rev3_ext_none. exact He.
Qed.

(** ** The invariant after the updates the runtime makes *)

(** A record is replaced by one that agrees with the monitor. *)
Lemma rev3_inv_put : forall m s g,
  Inv m s -> fid g < next_fid s ->
  (begun g = true -> In (fid g) (mreg m)) ->
  (begun g = false -> ~ In (fid g) (mreg m) /\ status g = Ready) ->
  (In (fid g) (mex m) -> status g = Finished) ->
  (forall tok, In (fid g, tok) (mpend m) -> status g = Await tok) ->
  Inv m (put g s).
Proof.
  intros m s g H Hf Hb Hn He Hp. destruct H.
  constructor; simpl.
  - apply rev3_nodup_put. assumption.
  - intros f h Hl. rewrite rev3_look_put in Hl. destruct (f =? fid g) eqn:E; [|eauto].
    apply Nat.eqb_eq in E. subst. exact Hf.
  - assumption.
  - intros f h Hl. rewrite rev3_look_put in Hl. destruct (f =? fid g) eqn:E; [|eauto].
    apply Nat.eqb_eq in E. injection Hl as <-. subst. exact Hb.
  - intros f h Hl. rewrite rev3_look_put in Hl. destruct (f =? fid g) eqn:E; [|eauto].
    apply Nat.eqb_eq in E. injection Hl as <-. subst. exact Hn.
  - intros f Hin. rewrite rev3_look_put. destruct (f =? fid g) eqn:E; [|eauto].
    apply Nat.eqb_eq in E. subst. exists g. split; [reflexivity|]. exact (He Hin).
  - intros f tok Hin. rewrite rev3_look_put. destruct (f =? fid g) eqn:E; [|eauto].
    apply Nat.eqb_eq in E. subst. exists g. split; [reflexivity|]. exact (Hp tok Hin).
  - assumption.
  - assumption.
  - assumption.
  - intros H0. rewrite rev3_look_put. destruct (0 =? fid g); [discriminate|]. auto.
  - assumption.
Qed.

(** A running fiber puts its own record back, in any status but finished or awaiting. *)
Lemma rev3_inv_put_running : forall m s g g',
  Inv m s -> Pre m s g -> fid g' = fid g -> begun g' = true ->
  status g' <> Finished -> (forall tok, status g' <> Await tok) ->
  Inv m (put g' s).
Proof.
  intros m s g g' H P Hid Hb Hnf Hna. destruct P.
  apply rev3_inv_put; rewrite ?Hid.
  - exact H.
  - exact p_fid0.
  - intros _. exact p_reg0.
  - intros Hb'. congruence.
  - intros Hin. destruct (i_ex _ _ H _ Hin) as [h [Hl Hs]]. exfalso. exact (p_live0 h Hl Hs).
  - intros tok Hin. destruct (p_pend0 tok Hin).
Qed.

Lemma rev3_pre_running : forall m s g g',
  Pre m s g -> fid g' = fid g -> begun g' = true -> status g' = Ready -> Pre m s g'.
Proof.
  intros m s g g' P Hid Hb Hr. destruct P. constructor; rewrite ?Hid; auto.
Qed.

(** The monitor state after a task: only open awaits change. *)
Lemma rev3_inv_pend_shrink : forall m m' s,
  Inv m s -> mreg m' = mreg m -> mex m' = mex m -> mtoks m' = mtoks m -> mrx m' = mrx m ->
  mfirst m' = mfirst m -> incl (mpend m') (mpend m) -> Inv m' s.
Proof.
  intros m m' s H Hr He Ht Hx Hf Hp. destruct H.
  constructor; rewrite ?Hr, ?He, ?Ht, ?Hx, ?Hf; auto.
Qed.

Lemma rev3_inv_task : forall m s t, Inv m s -> Inv (mnext m (LTask t)) s.
Proof.
  intros m s t H. apply (rev3_inv_pend_shrink m); try reflexivity; [exact H| |].
  { apply rev3_mfirst_other. exact I. }
  intros x Hx. destruct x as [g tok]. exact (proj1 (rev3_pend_task _ _ _ _ Hx)).
Qed.

Lemma rev3_inv_release : forall m s f tok,
  Inv m s -> Inv (mnext m (LEvent (EvRelease f tok))) s.
Proof.
  intros m s f tok H. apply (rev3_inv_pend_shrink m); try reflexivity; [exact H| |].
  { apply rev3_mfirst_other. exact I. }
  intros x Hx. destruct x as [g t]. exact (proj1 (rev3_pend_release _ _ _ _ _ Hx)).
Qed.

(** Entries that change nothing in the monitor. *)
Lemma rev3_mnext_quiet : forall m e,
  (match e with LClock _ _ | LDraw _ _ | LEvent (EvQueue _ _) => True | _ => False end) ->
  mnext m e = m.
Proof.
  intros m e Hk.
  assert (Hf : filter (still_open e) (mpend m) = mpend m).
  { apply forallb_filter_id. apply forallb_forall. intros [g' t'] _. unfold still_open.
    destruct e as [|[]| | |]; try destruct Hk; reflexivity. }
  destruct m as [r x p t b fs].
  destruct e as [|[]| | |]; try destruct Hk; unfold mnext; simpl in *; rewrite Hf;
    destruct fs; reflexivity.
Qed.

(** The monitor answers for a running fiber's clock reads and draws. *)
Lemma rev3_mok_running : forall m s g e,
  Inv m s -> Pre m s g -> entry_fiber e = Some (fid g) ->
  (match e with LClock _ _ | LDraw _ _ | LEvent (EvFiberExited _) => True | _ => False end) ->
  mok m e.
Proof.
  intros m s g e H P Hf Hk. destruct P.
  apply (rev3_mok_fiber _ (fid g)); [exact Hf| |exact p_reg0| |exact p_pend0].
  - destruct e as [|[]| | |]; try destruct Hk; exact I.
  - intros Hin. destruct (i_ex _ _ H _ Hin) as [h [Hl Hs]]. exact (p_live0 h Hl Hs).
Qed.

Lemma rev3_not_exited : forall m s g, Inv m s -> Pre m s g -> ~ In (fid g) (mex m).
Proof.
  intros m s g H P Hin. destruct (i_ex _ _ H _ Hin) as [h [Hl Hs]].
  exact (p_live _ _ _ P h Hl Hs).
Qed.

(** ** Scripts *)

Lemma rev3_wp_sbind : forall A B (s : Script A) (k : A -> Script B) m Q,
  wp m s (fun m' x => wp m' (k x) Q) -> wp m (sbind s k) Q.
Proof.
  intros A B s k. induction s as [x|e s IH|f s IH|f s IH|f s IH]; intros m Q H; simpl in *.
  - exact H.
  - destruct H as [Hok H]. exact (conj Hok (IH _ _ H)).
  - intros l. destruct (H l) as [Hok H']. exact (conj Hok (IH l _ _ H')).
  - intros l. destruct (H l) as [Hok H']. exact (conj Hok (IH l _ _ H')).
  - intros l. destruct (H l) as [Hok H']. exact (conj Hok (IH l _ _ H')).
Qed.

Lemma rev3_wp_enqueue : forall m s g p (Q : Mon -> CState -> Prop),
  (queued g = true -> Q m s) ->
  (queued g = false -> Q m (put (set_queued g true) s)) ->
  wp m (Concrete.enqueue s g p) Q.
Proof.
  intros m s g p Q Ht Hf. unfold Concrete.enqueue.
  destruct (queued g) eqn:E; [exact (Ht eq_refl)|].
  simpl. split; [apply rev3_mok_queue|]. rewrite rev3_mnext_quiet by exact I.
  exact (Hf eq_refl).
Qed.

Lemma rev3_set_queued_fields : forall g q,
  fid (set_queued g q) = fid g /\ begun (set_queued g q) = begun g /\
  status (set_queued g q) = status g.
Proof. intros. repeat split. Qed.
