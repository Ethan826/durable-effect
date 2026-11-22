(** * The concrete runtime's [go] and [interrupt] keep the invariant.

    One induction on the fuel covers both functions: [interrupt] with fuel [S n] calls [go]
    with fuel [n], and [go] with fuel [S n] calls both with fuel [n]. Proofs of the rev3
    domain. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Concrete Rev3Monitor Rev3ConcreteBase Rev3ConcreteSteps.
Import ListNotations.
Open Scope nat_scope.

Definition GoOK (fuel : nat) : Prop :=
  forall ops s g m, Inv m s -> Pre m s g -> wp m (go fuel ops s g) (Post m s (Some (fid g))).

Definition IntOK (fuel : nat) : Prop :=
  forall s t m, Inv m s -> wp m (interrupt fuel s t) (Post m s None).

(** ** Composing what scripts keep *)

Lemma rev3_post_refl : forall m s w, Inv m s -> Post m s w m s.
Proof.
  intros m s w H. split; [exact H|split; [apply rev3_ext_refl|intros x Hx; exact Hx]].
Qed.

Lemma rev3_ext_strengthen : forall s0 s1 f,
  Ext s0 (Some f) s1 -> (forall h, look f s0 = Some h -> status h <> Ready) -> Ext s0 None s1.
Proof.
  intros s0 s1 f [A [B C]] Hn. split; [exact A|split; [exact B|]].
  intros x h _ Hl Hr. destruct (Nat.eq_dec x f) as [->|Hne].
  - exfalso. exact (Hn h Hl Hr).
  - apply (C x h); [congruence|exact Hl|exact Hr].
Qed.

Lemma rev3_ext_trans_gen : forall s0 s1 s2 w0 w1,
  Ext s0 w0 s1 -> Ext s1 w1 s2 ->
  (forall f h, look f s0 = Some h -> w1 = Some f -> w0 = Some f) -> Ext s0 w0 s2.
Proof.
  intros s0 s1 s2 w0 w1 [A1 [B1 C1]] [A2 [B2 C2]] Hw. split; [lia|split].
  - intros f h H. destruct (B1 _ _ H) as [h1 H1]. exact (B2 _ _ H1).
  - intros f h Hn H Hr. destruct (C1 _ _ Hn H Hr) as [h1 [H1 Hr1]].
    apply (C2 _ _ ltac:(intro E; exact (Hn (Hw _ _ H E))) H1 Hr1).
Qed.

Lemma rev3_incl_trans : forall (a b c : list FiberId), incl a b -> incl b c -> incl a c.
Proof. intros a b c H1 H2 x Hx. exact (H2 _ (H1 _ Hx)). Qed.

Lemma rev3_incl_filter : forall A (p : A -> bool) l, incl (filter p l) l.
Proof. intros A p l x Hx. apply filter_In in Hx. exact (proj1 Hx). Qed.

(** ** [interrupt] *)

Lemma rev3_post_flags : forall m s t g g',
  Inv m s -> look t s = Some g -> status g <> Finished ->
  fid g' = fid g -> begun g' = begun g -> status g' = status g ->
  Post m s None m (put g' s).
Proof.
  intros m s t g g' H Hl Hf Hid Hb Hs. destruct (rev3_look_some _ _ _ Hl) as [Ht _]. subst t.
  split; [|split; [apply rev3_ext_put_ready; intros h Hh Hr; rewrite Hid, Hl in Hh;
    congruence|intros x Hx; exact Hx]].
  apply rev3_inv_put; rewrite ?Hid, ?Hb, ?Hs; [exact H|exact (i_fid _ _ H _ _ Hl)|..].
  - exact (i_begun _ _ H _ _ Hl).
  - exact (i_fresh _ _ H _ _ Hl).
  - intros Hin. destruct (i_ex _ _ H _ Hin) as [h [Hh Hs']]. rewrite Hl in Hh. congruence.
  - intros tok Hin. destruct (i_pend _ _ H _ _ Hin) as [h [Hh Hs']]. rewrite Hl in Hh.
    congruence.
Qed.

Lemma rev3_interrupt_step : forall fuel, GoOK fuel -> IntOK (S fuel).
Proof.
  intros fuel Hgo s t m H. cbn [interrupt].
  destruct (look t s) as [g|] eqn:Hl; [|exact (rev3_post_refl m s None H)].
  destruct (rev3_look_some _ _ _ Hl) as [Hid _].
  destruct (unwinding g) eqn:Hu; [exact (rev3_post_refl m s None H)|].
  assert (Hun : forall e m', status g <> Ready -> Inv m' s -> incl (mreg m) (mreg m') ->
            Pre m' s (unwind g e) -> wp m' (go fuel 0 s (unwind g e)) (Post m s None)).
  { intros e m' Hnr H' Hi P. refine (rev3_wp_mono _ _ _ _ _ _ (Hgo 0 s (unwind g e) m' H' P)).
    intros m'' s' [Hi' [He Hr]]. split; [exact Hi'|split; [|exact (rev3_incl_trans _ _ _ Hi Hr)]].
    destruct (rev3_unwind_fields g e) as [F1 _]. rewrite F1, Hid in He.
    apply (rev3_ext_strengthen _ _ t He). intros h Hh. rewrite Hl in Hh.
    injection Hh as <-. exact Hnr. }
  assert (Hpre : forall e m', Inv m' s -> status g <> Ready -> status g <> Finished ->
            no_pend m' t -> Pre m' s (unwind g e)).
  { intros e m' H' Hnr Hnf Hnp. destruct (rev3_unwind_fields g e) as [F1 [F2 F3]].
    apply (rev3_pre_of_record m' s t g (unwind g e) H' Hl
      (rev3_begun_record m' s t g H' Hl Hnr) Hnf Hnp);
      [congruence|rewrite F2; exact (rev3_begun_record m' s t g H' Hl Hnr)|exact F3]. }
  destruct (status g) as [|tok|cell|target|] eqn:Hs.
  - destruct (negb (mask g =? 0));
      (apply rev3_post_flags with (t := t) (g := g); [exact H|exact Hl|rewrite Hs; discriminate|reflexivity..]).
  - destruct (negb (mask g =? 0));
      [apply rev3_post_flags with (t := t) (g := g); [exact H|exact Hl|rewrite Hs; discriminate|reflexivity..]|].
    simpl. split.
    + apply rev3_mok_release.
      * apply (i_begun _ _ H _ _ Hl). apply (rev3_begun_record m s t g H Hl). congruence.
      * intros Hin. destruct (i_ex _ _ H _ Hin) as [h [Hh Hf]]. rewrite Hl in Hh.
        injection Hh as <-. congruence.
      * intros t' Hin. destruct (i_pend _ _ H _ _ Hin) as [h [Hh Hf]]. rewrite Hl in Hh.
        injection Hh as <-. congruence.
    + pose proof (rev3_inv_release m s t tok H) as H1.
      apply Hun; [congruence|exact H1|intros x Hx; exact Hx|].
      apply Hpre; [exact H1|congruence|congruence|].
      intros t' Hin. apply rev3_pend_release in Hin. destruct Hin as [Hin Hne].
      destruct (i_pend _ _ H _ _ Hin) as [h [Hh Hf]]. rewrite Hl in Hh. injection Hh as <-.
      apply Hne. split; congruence.
  - destruct (negb (mask g =? 0));
      [apply rev3_post_flags with (t := t) (g := g); [exact H|exact Hl|rewrite Hs; discriminate|reflexivity..]|].
    apply Hun; [congruence|exact H|intros x Hx; exact Hx|].
    apply Hpre; [exact H|congruence|congruence|].
    apply (rev3_no_pend_record m s t g H Hl). congruence.
  - destruct (negb (mask g =? 0));
      [apply rev3_post_flags with (t := t) (g := g); [exact H|exact Hl|rewrite Hs; discriminate|reflexivity..]|].
    apply Hun; [congruence|exact H|intros x Hx; exact Hx|].
    apply Hpre; [exact H|congruence|congruence|].
    apply (rev3_no_pend_record m s t g H Hl). congruence.
  - exact (rev3_post_refl m s None H).
Qed.


(** ** [go] *)

(** A fiber's finalizer has returned: it exits, the root's exit is reported, and fibers
    waiting for it are woken. *)
Lemma rev3_go_exit : forall m s g v, Inv m s -> Pre m s g ->
  wp m (sbind (if fid g =? 0
               then Emit (EvFiberExited 0) (Emit (EvRootExit (exit g))
                      (Done (put (with_code g (CEnd v) Finished) s)))
               else Emit (EvFiberExited (fid g)) (Done (put (with_code g (CEnd v) Finished) s)))
              (fun s'' => wake_exit s'' (fid g)))
    (Post m s (Some (fid g))).
Proof.
  intros m s g v H P. apply rev3_wp_sbind.
  set (g' := with_code g (CEnd v) Finished).
  assert (Hwake : forall m', Inv m' (put g' s) -> mreg m' = mreg m ->
            wp m' (wake_exit (put g' s) (fid g)) (Post m s (Some (fid g)))).
  { intros m' H' Hr.
    refine (rev3_wp_mono _ _ _ _ _ _ (rev3_wake_exit_ok (put g' s) m' (fid g) H')).
    intros m'' s'' [-> [Hi He]]. split; [exact Hi|split].
    - apply (rev3_ext_trans _ (put g' s)); [exact (rev3_ext_put g' s)|].
      apply rev3_ext_none. exact He.
    - rewrite Hr. intros x Hx. exact Hx. }
  pose proof (rev3_not_exited m s g H P) as Hne.
  pose proof (rev3_first_root m s _ H (p_reg _ _ _ P)) as Hfirst.
  destruct (fid g =? 0) eqn:E0.
  - apply Nat.eqb_eq in E0. cbn [wp]. split.
    + pose proof (rev3_mok_running m s g (LEvent (EvFiberExited (fid g))) H P eq_refl I) as Hk.
      rewrite E0 in Hk. exact Hk.
    + split.
      * apply (rev3_mok_root _ _ 0).
        -- simpl. destruct (mrx m) eqn:Ex; [|reflexivity].
           exfalso. apply Hne. rewrite E0. exact (i_rx _ _ H Ex).
        -- simpl. rewrite Hfirst. reflexivity.
        -- simpl. left. reflexivity.
      * apply Hwake; [|reflexivity]. apply (rev3_inv_exit m); [exact H|exact P|reflexivity|..].
        -- simpl. rewrite E0. reflexivity.
        -- simpl. intros x Hx. apply filter_In in Hx. destruct Hx as [Hx _].
           apply filter_In in Hx. exact (proj1 Hx).
        -- reflexivity.
        -- intros _. right. exact E0.
        -- simpl. rewrite Hfirst. reflexivity.
  - cbn [wp]. split.
    + exact (rev3_mok_running m s g (LEvent (EvFiberExited (fid g))) H P eq_refl I).
    + apply Hwake; [|reflexivity]. apply (rev3_inv_exit m); [exact H|exact P|reflexivity|..].
      * reflexivity.
      * simpl. apply rev3_incl_filter.
      * reflexivity.
      * intros Hx. left. exact Hx.
      * apply rev3_mfirst_other. exact I.
Qed.

Lemma rev3_go_zero : GoOK 0 /\ IntOK 0.
Proof.
  split.
  - intros ops s g m H P. cbn [go].
    apply rev3_post_park; [exact H|exact P|reflexivity|exact (p_begun _ _ _ P)|
      exact (p_ready _ _ _ P)].
  - intros s t m H. cbn [interrupt]. exact (rev3_post_refl m s None H).
Qed.

(** After a nested script, a fiber whose record is still ready continues. *)
Lemma rev3_resume_ready : forall fuel ops m0 s0 m s f p,
  GoOK fuel -> Inv m s -> look f s = Some p -> status p = Ready -> In f (mreg m) ->
  Ext s0 (Some f) s -> incl (mreg m0) (mreg m) ->
  wp m (go fuel ops s p) (Post m0 s0 (Some f)).
Proof.
  intros fuel ops m0 s0 m s f p Hgo H Hl Hr Hreg He Hi.
  destruct (rev3_look_some _ _ _ Hl) as [Hid _].
  refine (rev3_wp_mono _ _ _ _ _ _ (Hgo ops s p m H (rev3_pre_ready m s f p H Hl Hr Hreg))).
  intros m' s' Hpost. rewrite Hid in Hpost. exact (rev3_post_trans _ _ _ _ _ _ _ He Hi Hpost).
Qed.

Lemma rev3_go_step : forall fuel, GoOK fuel -> IntOK fuel -> GoOK (S fuel).
Proof.
  intros fuel Hgo Hint ops s g m H P. cbn [go].
  destruct (max_ops <=? ops).
  { apply rev3_post_park; [exact H|exact P|reflexivity|exact (p_begun _ _ _ P)|
      exact (p_ready _ _ _ P)]. }
  assert (Hcont : forall ops' g', fid g' = fid g -> begun g' = true -> status g' = Ready ->
            wp m (go fuel ops' s g') (Post m s (Some (fid g)))).
  { intros ops' g' Hid Hb Hr. rewrite <- Hid. apply Hgo; [exact H|].
    exact (rev3_pre_running m s g g' P Hid Hb Hr). }
  assert (Hunw : forall ops' e, wp m (go fuel ops' s (unwind g e)) (Post m s (Some (fid g)))).
  { intros ops' e. destruct (rev3_unwind_fields g e) as [F1 [F2 F3]].
    apply Hcont; [exact F1|rewrite F2; exact (p_begun _ _ _ P)|exact F3]. }
  pose proof (p_begun _ _ _ P) as Hbg.
  destruct (intr g && (mask g =? 0) && negb (unwinding g)); [apply Hunw|].
  destruct (code g) as [v|v|k|k|op k|imm b k|pr k|c v k|c k|c k|t k|k|k] eqn:Hc.
  - (* CEnd *)
    destruct (unwinding g); [exact (rev3_go_exit m s g v H P)|apply Hunw].
  - (* CFail *)
    destruct (unwinding g); [exact (rev3_go_exit m s g v H P)|apply Hunw].
  - (* CClock *)
    cbn [wp]. intros l. split; [exact (rev3_mok_running m s g (LClock (fid g) l) H P eq_refl I)|].
    rewrite rev3_mnext_quiet by exact I. apply Hcont; reflexivity || exact Hbg.
  - (* CDraw *)
    cbn [wp]. intros r. split; [exact (rev3_mok_running m s g (LDraw (fid g) r) H P eq_refl I)|].
    rewrite rev3_mnext_quiet by exact I. apply Hcont; reflexivity || exact Hbg.
  - (* CStart *)
    cbn [wp]. exact (rev3_post_start m s g op k H P).
  - (* CFork *)
    set (c := next_fid s). set (child := new_fiber c (bodies (program s) b)).
    pose proof (rev3_look_fresh m s H) as Hfresh. fold c in Hfresh.
    assert (Hcg : c <> fid g) by (pose proof (p_fid _ _ _ P); unfold c; lia).
    destruct imm.
    + cbn [wp fid child new_fiber]. intros i. split; [exact (rev3_mok_register_fresh m s i H)|].
      set (m1 := mnext m (LRegister c i)).
      set (parent := with_code g (k c) Ready).
      set (child' := with_flags child 0 i false false true (exit child)).
      pose proof (rev3_inv_register_fresh m s i H (rev3_first_root m s _ H (p_reg _ _ _ P)))
        as H1. fold c m1 in H1.
      pose proof (rev3_pre_register_fresh m s g i H P) as P1. fold c m1 in P1.
      assert (H2 : Inv m1 (put parent (bump_fid s))).
      { apply (rev3_inv_put_running m1 (bump_fid s) g parent H1 P1); try reflexivity;
          [exact Hbg|discriminate|intros tok; discriminate]. }
      assert (Pc : Pre m1 (put parent (bump_fid s)) child').
      { constructor; cbn [fid child' child new_fiber with_flags begun status].
        - left. reflexivity.
        - intros h Hh. rewrite rev3_look_put_neq in Hh by exact Hcg.
          rewrite rev3_look_bump_fid, Hfresh in Hh. discriminate.
        - intros tok Hin. unfold m1 in Hin. rewrite rev3_pend_same in Hin by exact I.
          destruct (i_pend _ _ H _ _ Hin) as [h [Hh _]]. congruence.
        - simpl. unfold c. lia.
        - reflexivity.
        - reflexivity. }
      apply rev3_wp_sbind.
      refine (rev3_wp_mono _ _ _ _ _ _ (Hgo 0 _ child' m1 H2 Pc)).
      intros m2 s2 [H3 [E3 I3]].
      assert (Hpar : look (fid g) (put parent (bump_fid s)) = Some parent)
        by exact (rev3_look_put_eq parent (bump_fid s)).
      destruct (proj2 (proj2 E3) (fid g) parent ltac:(cbn [fid child' child new_fiber with_flags];
        intro E; injection E; exact Hcg) Hpar eq_refl) as [p [Hp Hpr]].
      rewrite Hp.
      apply (rev3_resume_ready fuel (S ops) m s m2 s2 (fid g) p Hgo H3 Hp Hpr).
      * apply I3. right. exact (p_reg _ _ _ P).
      * apply (rev3_ext_trans_gen _ (put parent (bump_fid s)) _ _ (Some c)); [|exact E3|].
        -- apply (rev3_ext_trans _ (bump_fid s)).
           ++ apply rev3_ext_none. apply rev3_ext_same_fibers; [reflexivity|simpl; lia].
           ++ exact (rev3_ext_put parent (bump_fid s)).
        -- intros f h Hl E. injection E as <-. congruence.
      * intros x Hx. apply I3. right. exact Hx.
    + apply rev3_wp_sbind. apply rev3_wp_enqueue; [intros Hq; discriminate Hq|intros _].
      set (s1 := bump_fid s).
      assert (Hc1 : forall x, In x (mreg m) -> x <> c).
      { intros x Hx E. pose proof (i_reg _ _ H _ Hx). unfold c in E. lia. }
      assert (Hput : forall s' ch, Inv m s' -> fid ch = c -> begun ch = false ->
                status ch = Ready -> c < next_fid s' -> Inv m (put ch s')).
      { intros s' ch Hs' Hid Hb Hr Hlt. apply rev3_inv_put; rewrite ?Hid; [exact Hs'|exact Hlt|..].
        - intros Hb'. congruence.
        - intros _. split; [intro Hx; exact (Hc1 c Hx eq_refl)|exact Hr].
        - intros Hin. destruct (i_ex _ _ H _ Hin) as [h [Hh _]]. congruence.
        - intros tok Hin. destruct (i_pend _ _ H _ _ Hin) as [h [Hh _]]. congruence. }
      assert (H1 : Inv m s1).
      { apply (rev3_inv_same_fibers m s); simpl; auto.
        right. exact (rev3_first_root m s _ H (p_reg _ _ _ P)). }
      assert (H2 : Inv m (put child s1)) by (apply Hput; [exact H1|reflexivity..|simpl; unfold c; lia]).
      set (s2 := put (set_queued child true) (put child s1)).
      assert (H3 : Inv m s2) by (apply Hput; [exact H2|reflexivity..|simpl; unfold c; lia]).
      assert (Hl2 : look (fid g) s2 = look (fid g) s).
      { unfold s2. rewrite !rev3_look_put_neq by (simpl; intro E; apply Hcg; symmetry; exact E).
        reflexivity. }
      assert (P2 : Pre m s2 (with_code g (k (fid child)) Ready)).
      { destruct P as [Pr Pl Pp Pf Pb Prd]. constructor; cbn [fid with_code begun status].
        - exact Pr.
        - intros h Hh. rewrite Hl2 in Hh. exact (Pl h Hh).
        - exact Pp.
        - unfold s2, s1. simpl. lia.
        - exact Pb.
        - reflexivity. }
      refine (rev3_wp_mono _ _ _ _ _ _ (Hgo (S ops) s2 _ m H3 P2)).
      intros m' s' Hpost. apply (rev3_post_trans m s m s2); [|intros x Hx; exact Hx|exact Hpost].
      apply rev3_ext_none. apply (rev3_ext_trans _ s1).
      * apply rev3_ext_same_fibers; [reflexivity|simpl; lia].
      * apply (rev3_ext_trans _ (put child s1)).
        -- apply rev3_ext_put_ready. intros. reflexivity.
        -- apply rev3_ext_put_ready. intros. reflexivity.
  - (* CYield *)
    apply rev3_post_park; [exact H|exact P|reflexivity|exact Hbg|reflexivity].
  - (* CWrite *)
    set (s0 := set_cell s c v). set (g1 := with_code g k Ready). set (s1 := put g1 s0).
    assert (H0 : Inv m s0) by (apply (rev3_inv_same_fibers m s); simpl; auto).
    assert (P0 : Pre m s0 g) by (apply (rev3_pre_same_fibers m s); simpl; auto).
    assert (H1 : Inv m s1).
    { apply (rev3_inv_put_running m s0 g g1 H0 P0); try reflexivity;
        [exact Hbg|discriminate|intros tok; discriminate]. }
    apply rev3_wp_sbind.
    assert (Hw : wp m (if v =? 0 then Done s1 else wake_cell s1 c v)
                   (fun m' s' => m' = m /\ Inv m s' /\ Ext s1 None s')).
    { destruct (v =? 0); [split; [reflexivity|split; [exact H1|apply rev3_ext_refl]]|].
      exact (rev3_wake_cell_ok s1 m c v H1). }
    refine (rev3_wp_mono _ _ _ _ _ _ Hw). intros m' s2 [-> [H2 E2]].
    assert (Hl1 : look (fid g) s1 = Some g1) by exact (rev3_look_put_eq g1 s0).
    destruct (proj2 (proj2 E2) (fid g) g1 ltac:(discriminate) Hl1 eq_refl) as [p [Hp Hpr]].
    rewrite Hp.
    apply (rev3_resume_ready fuel (S ops) m s m s2 (fid g) p Hgo H2 Hp Hpr (p_reg _ _ _ P));
      [|intros x Hx; exact Hx].
    apply (rev3_ext_trans _ s1).
    + apply (rev3_ext_trans _ s0).
      * apply rev3_ext_none. apply rev3_ext_same_fibers; [reflexivity|simpl; lia].
      * exact (rev3_ext_put g1 s0).
    + apply rev3_ext_none. exact E2.
  - (* CRead *)
    apply Hcont; reflexivity || exact Hbg.
  - (* CAwaitCell *)
    destruct (cells s c =? 0); [|apply Hcont; reflexivity || exact Hbg].
    cbn [wp]. apply rev3_post_put_running; [exact H|exact P|reflexivity|exact Hbg|
      discriminate|intros tok; discriminate].
  - (* CInterrupt *)
    set (w := with_code g k (OnExit t)). set (s1 := put w s).
    assert (H1 : Inv m s1).
    { apply (rev3_inv_put_running m s g w H P); try reflexivity;
        [exact Hbg|discriminate|intros tok; discriminate]. }
    assert (Hw : look (fid g) s1 = Some w) by exact (rev3_look_put_eq w s).
    assert (E1 : Ext s (Some (fid g)) s1) by exact (rev3_ext_put w s).
    (* the waiting fiber resumes from its record *)
    assert (Hres : forall m2 s2 p, Inv m2 s2 -> look (fid g) s2 = Some p ->
              (exists x, status p = OnExit x) -> Ext s1 None s2 -> incl (mreg m) (mreg m2) ->
              wp m2 (go fuel (S ops) s2 (with_code p (code p) Ready)) (Post m s (Some (fid g)))).
    { intros m2 s2 p H2 Hp [x Hx] E2 I2.
      destruct (rev3_look_some _ _ _ Hp) as [Hid _].
      assert (Pp : Pre m2 s2 (with_code p (code p) Ready)).
      { apply (rev3_pre_of_record m2 s2 (fid g) p _ H2 Hp); cbn [fid begun status with_code].
        - apply (rev3_begun_record m2 s2 (fid g) p H2 Hp). congruence.
        - congruence.
        - apply (rev3_no_pend_record m2 s2 (fid g) p H2 Hp). congruence.
        - exact Hid.
        - apply (rev3_begun_record m2 s2 (fid g) p H2 Hp). congruence.
        - reflexivity. }
      refine (rev3_wp_mono _ _ _ _ _ _ (Hgo (S ops) s2 _ m2 H2 Pp)).
      intros m3 s3 Hpost. cbn [fid with_code] in Hpost. rewrite Hid in Hpost.
      apply (rev3_post_trans m s m2 s2); [|exact I2|exact Hpost].
      apply (rev3_ext_trans _ s1); [exact E1|apply rev3_ext_none; exact E2]. }
    apply rev3_wp_sbind.
    destruct (look t s1) as [tg0|] eqn:Ht0.
    + refine (rev3_wp_mono _ _ _ _ _ _ (Hint s1 t m H1)).
      intros m2 s2 [H2 [E2 I2]].
      destruct (proj1 (proj2 E2) (fid g) w Hw) as [p Hp].
      destruct (proj1 (proj2 E2) t tg0 Ht0) as [tg Htg].
      rewrite Hp, Htg.
      assert (Hdone : Post m s (Some (fid g)) m2 s2).
      { split; [exact H2|split; [|exact I2]].
        apply (rev3_ext_trans _ s1); [exact E1|apply rev3_ext_none; exact E2]. }
      destruct (status tg); try exact Hdone.
      destruct (status p) eqn:Hsp; try exact Hdone.
      apply (Hres m2 s2 p H2 Hp); [exists target; exact Hsp|exact E2|exact I2].
    + assert (Hd : interrupt fuel s1 t = Done s1)
        by (destruct fuel; [reflexivity|cbn [interrupt]; rewrite Ht0; reflexivity]).
      rewrite Hd. cbn [wp]. rewrite Hw, Ht0.
      apply (Hres m s1 w H1 Hw); [exists t; reflexivity|apply rev3_ext_refl|intros x Hx; exact Hx].
  - (* CMaskOn *)
    apply Hcont; reflexivity || exact Hbg.
  - (* CMaskOff *)
    apply Hcont; reflexivity || exact Hbg.
Qed.

Theorem rev3_go_ok : forall fuel, GoOK fuel /\ IntOK fuel.
Proof.
  induction fuel as [|fuel [Hgo Hint]]; [exact rev3_go_zero|].
  split; [exact (rev3_go_step fuel Hgo Hint)|exact (rev3_interrupt_step fuel Hgo)].
Qed.
