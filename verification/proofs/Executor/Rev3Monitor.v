(** * A log monitor for the interface properties I4, I6, I7 and I8.

    The properties are stated over every split of a log. This file checks them left to right
    instead: a monitor state records the fibers started and exited, the awaits still open,
    the tokens started and whether the root has exited. A log the monitor accepts meets I4,
    I6, I7 and I8 ([rev3_mrun_props]). A weakest-precondition predicate over scripts then
    reduces the properties of a runtime to an invariant of its state that every task keeps
    ([rev3_meets_of_monitor]). Proofs of the rev3 domain. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime.
Import ListNotations.

(** ** The monitor *)

Record Mon := {
  mreg : list FiberId;
  mex : list FiberId;
  mpend : list (FiberId * Token);
  mtoks : list Token;
  mrx : bool;
  mfirst : option FiberId
}.

Definition m0 : Mon :=
  {| mreg := []; mex := []; mpend := []; mtoks := []; mrx := false; mfirst := None |}.

(** Whether entry [e] may come next. *)
Definition mok (m : Mon) (e : LogEntry) : Prop :=
  (forall f, entry_fiber e = Some f ->
     (In f (mreg m) \/ exists b, e = LRegister f b) /\ ~ In f (mex m) /\
     (forall tok, In (f, tok) (mpend m) -> ends_await f tok e = true)) /\
  (forall f b, e = LRegister f b -> ~ In f (mreg m)) /\
  (forall f tok op, e = LEvent (EvStart f tok op) -> ~ In tok (mtoks m)) /\
  (forall r, e = LEvent (EvRootExit r) -> mrx m = false) /\
  (forall r, e = LEvent (EvRootExit r) -> exists f, mfirst m = Some f /\ In f (mex m)).

Definition still_open (e : LogEntry) (p : FiberId * Token) : bool :=
  negb (ends_await (fst p) (snd p) e).

Definition mnext (m : Mon) (e : LogEntry) : Mon :=
  {| mreg := match e with LRegister f _ => f :: mreg m | _ => mreg m end;
     mex := match e with LEvent (EvFiberExited f) => f :: mex m | _ => mex m end;
     mpend := match e with LEvent (EvStart f tok _) => [(f, tok)] | _ => [] end ++
              filter (still_open e) (mpend m);
     mtoks := match e with LEvent (EvStart _ tok _) => tok :: mtoks m | _ => mtoks m end;
     mrx := match e with LEvent (EvRootExit _) => true | _ => mrx m end;
     mfirst := match mfirst m with
               | Some f => Some f
               | None => match e with LRegister f _ => Some f | _ => None end
               end |}.

Fixpoint mrun (m : Mon) (log : list LogEntry) : Prop :=
  match log with
  | [] => True
  | e :: rest => mok m e /\ mrun (mnext m e) rest
  end.

Definition mfold (m : Mon) (log : list LogEntry) : Mon := fold_left mnext log m.

Lemma rev3_mrun_app : forall l1 l2 m,
  mrun m (l1 ++ l2) <-> mrun m l1 /\ mrun (mfold m l1) l2.
Proof.
  induction l1 as [|e l1 IH]; intros l2 m; simpl.
  - tauto.
  - rewrite IH. unfold mfold. simpl. tauto.
Qed.

(** ** From an accepted log to the properties *)

Lemma rev3_mrun_started : forall log m, mrun m log ->
  NoDup (started log) /\ forall f, In f (started log) -> ~ In f (mreg m).
Proof.
  induction log as [|e log IH]; intros m Hrun; [simpl; split; [constructor|tauto]|destruct Hrun as [Hok Hrun]].
  destruct (IH _ Hrun) as [Hnd Hnot].
  destruct Hok as [_ [Hreg _]].
  destruct e as [t|ev|f l|f r|f b]; simpl in *; try (split; [exact Hnd|]; intros g Hg;
    specialize (Hnot g Hg); exact Hnot).
  split.
  - constructor; [|exact Hnd]. intro Hin. apply (Hnot f Hin). left. reflexivity.
  - intros g [Heq|Hg]; [subst g; exact (Hreg f b eq_refl)|].
    intro Hm. apply (Hnot g Hg). right. exact Hm.
Qed.

Lemma rev3_mrun_tokens : forall log m, mrun m log ->
  NoDup (start_tokens log) /\ forall tok, In tok (start_tokens log) -> ~ In tok (mtoks m).
Proof.
  induction log as [|e log IH]; intros m Hrun; [simpl; split; [constructor|tauto]|destruct Hrun as [Hok Hrun]].
  destruct (IH _ Hrun) as [Hnd Hnot].
  destruct Hok as [_ [_ [Htok _]]].
  destruct e as [t|ev|f l|f r|f b];
    [| destruct ev as [f tok op|f tok|p t|f|r] | | |]; simpl in *;
    try (split; [exact Hnd|]; intros g Hg; exact (Hnot g Hg)).
  split.
  - constructor; [|exact Hnd]. intro Hin. apply (Hnot tok Hin). left. reflexivity.
  - intros g [Heq|Hg]; [subst g; exact (Htok f tok op eq_refl)|].
    intro Hm. apply (Hnot g Hg). right. exact Hm.
Qed.

Lemma rev3_mrun_exits : forall log m, mrun m log ->
  (root_exits log <= if mrx m then 0 else 1)%nat.
Proof.
  unfold root_exits.
  induction log as [|e log IH]; intros m Hrun; [simpl; lia|destruct Hrun as [Hok Hrun]].
  specialize (IH _ Hrun). destruct Hok as [_ [_ [_ [Hrx _]]]].
  destruct e as [t|ev|f l|f r|f b];
    [| destruct ev as [f tok op|f tok|p t|f|r] | | |]; simpl in *; try exact IH.
  rewrite (Hrx r eq_refl) in *. simpl in IH. lia.
Qed.

Lemma rev3_mrun_quiet : forall post m f tok, In (f, tok) (mpend m) -> mrun m post ->
  quiet_until_end f tok post.
Proof.
  induction post as [|e post IH]; intros m f tok Hin Hrun; simpl; [exact I|destruct Hrun as [Hok Hrun]].
  destruct (ends_await f tok e) eqn:He; [exact I|].
  split.
  - intro Hf. destruct Hok as [Hfib _]. destruct (Hfib f Hf) as [_ [_ Hp]].
    rewrite (Hp tok Hin) in He. discriminate.
  - apply (IH (mnext m e)); [|exact Hrun].
    simpl. apply in_or_app. right. apply filter_In. split; [exact Hin|].
    unfold still_open. simpl. rewrite He. reflexivity.
Qed.

Lemma rev3_mfold_reg : forall pre m f, In f (mreg (mfold m pre)) ->
  In f (mreg m) \/ exists b, In (LRegister f b) pre.
Proof.
  induction pre as [|e pre IH]; intros m f Hin; [left; exact Hin|].
  destruct (IH _ _ Hin) as [H|[b Hb]]; [|right; exists b; right; exact Hb].
  destruct e; simpl in H; try (left; exact H).
  destruct H as [<-|H]; [right; exists interrupted; left; reflexivity|left; exact H].
Qed.

Lemma rev3_mfold_ex : forall pre m f, In (LEvent (EvFiberExited f)) pre \/ In f (mex m) ->
  In f (mex (mfold m pre)).
Proof.
  induction pre as [|e pre IH]; intros m f H.
  - destruct H as [[]|H]; exact H.
  - unfold mfold. simpl. fold (mfold (mnext m e) pre). apply IH.
    destruct H as [[He|H]|H].
    + subst e. right. simpl. left. reflexivity.
    + left. exact H.
    + right. destruct e as [t|ev|g l|g r|g b];
        [| destruct ev | | |]; simpl; auto.
Qed.

(** An accepted log meets the properties. *)
Theorem rev3_mrun_props : forall log, mrun m0 log ->
  (forall pre f tok op post, log = pre ++ LEvent (EvStart f tok op) :: post ->
     quiet_until_end f tok post) /\
  NoDup (start_tokens log) /\
  (root_exits log <= 1)%nat /\
  NoDup (started log) /\
  (forall pre e post f, log = pre ++ e :: post -> entry_fiber e = Some f ->
     (exists b, e = LRegister f b \/ In (LRegister f b) pre) /\
     ~ In (LEvent (EvFiberExited f)) pre).
Proof.
  intros log Hrun. split; [|split; [|split; [|split]]].
  - intros pre f tok op post ->. apply rev3_mrun_app in Hrun. destruct Hrun as [_ [_ Hrun]].
    apply (rev3_mrun_quiet post (mnext (mfold m0 pre) (LEvent (EvStart f tok op))) f tok);
      [|exact Hrun].
    simpl. left. reflexivity.
  - exact (proj1 (rev3_mrun_tokens _ _ Hrun)).
  - exact (rev3_mrun_exits _ _ Hrun).
  - exact (proj1 (rev3_mrun_started _ _ Hrun)).
  - intros pre e post f -> Hf. apply rev3_mrun_app in Hrun. destruct Hrun as [_ [Hok _]].
    unfold mok in Hok. destruct Hok as [Hfib _]. destruct (Hfib f Hf) as [Hreg [Hex _]]. split.
    + destruct Hreg as [Hreg|[b Hb]].
      * destruct (rev3_mfold_reg _ _ _ Hreg) as [[]|[b Hb]]. exists b. right. exact Hb.
      * exists b. left. exact Hb.
    + intro Hin. apply Hex. apply rev3_mfold_ex. left. exact Hin.
Qed.

Lemma rev3_mfold_first : forall pre m,
  mfirst (mfold m pre) = match mfirst m with Some f => Some f | None => first_registered pre end.
Proof.
  induction pre as [|e pre IH]; intros m; [simpl; destruct (mfirst m); reflexivity|].
  unfold mfold. simpl. fold (mfold (mnext m e) pre). rewrite IH. simpl.
  destruct (mfirst m); [reflexivity|]. destruct e; reflexivity.
Qed.

Lemma rev3_mfold_ex_back : forall pre m f, In f (mex (mfold m pre)) ->
  In f (mex m) \/ In (LEvent (EvFiberExited f)) pre.
Proof.
  induction pre as [|e pre IH]; intros m f Hin; [left; exact Hin|].
  unfold mfold in Hin. simpl in Hin. fold (mfold (mnext m e) pre) in Hin.
  destruct (IH _ _ Hin) as [H|H]; [|right; right; exact H].
  destruct e as [t|[]| | |]; simpl in H; try (left; exact H).
  destruct H as [<-|H]; [right; left; reflexivity|left; exact H].
Qed.

(** An accepted log reports the root's exit only after the first fiber it registers has
    exited. *)
Theorem rev3_mrun_root_after : forall log, mrun m0 log ->
  forall pre e post, log = pre ++ LEvent (EvRootExit e) :: post ->
    exists r, first_registered pre = Some r /\ In (LEvent (EvFiberExited r)) pre.
Proof.
  intros log Hrun pre e post ->. apply rev3_mrun_app in Hrun. destruct Hrun as [_ [Hok _]].
  unfold mok in Hok. destruct Hok as [_ [_ [_ [_ Hf]]]].
  destruct (Hf e eq_refl) as [r [Hr Hex]]. exists r.
  rewrite rev3_mfold_first in Hr. simpl in Hr. split; [exact Hr|].
  destruct (rev3_mfold_ex_back _ _ _ Hex) as [[]|H]. exact H.
Qed.

(** ** Weakest preconditions over scripts *)

Fixpoint wp {St} (m : Mon) (s : Script St) (Q : Mon -> St -> Prop) : Prop :=
  match s with
  | Done x => Q m x
  | Emit e k => mok m (LEvent e) /\ wp (mnext m (LEvent e)) k Q
  | AskClock f k => forall l, mok m (LClock f l) /\ wp (mnext m (LClock f l)) (k l) Q
  | AskDraw f k => forall r, mok m (LDraw f r) /\ wp (mnext m (LDraw f r)) (k r) Q
  | Register f k => forall b, mok m (LRegister f b) /\ wp (mnext m (LRegister f b)) (k b) Q
  end.

Lemma rev3_wp_mono : forall St (s : Script St) m (Q Q' : Mon -> St -> Prop),
  (forall m' x, Q m' x -> Q' m' x) -> wp m s Q -> wp m s Q'.
Proof.
  intros St s. induction s as [x|e k IH|f k IH|f k IH|f k IH]; intros m Q Q' HQ H; simpl in *.
  - exact (HQ _ _ H).
  - destruct H as [Hok H]. exact (conj Hok (IH _ _ _ HQ H)).
  - intros l. destruct (H l) as [Hok H']. exact (conj Hok (IH l _ _ _ HQ H')).
  - intros l. destruct (H l) as [Hok H']. exact (conj Hok (IH l _ _ _ HQ H')).
  - intros l. destruct (H l) as [Hok H']. exact (conj Hok (IH l _ _ _ HQ H')).
Qed.

Lemma rev3_wp_play : forall St (s : Script St) m Q A c d,
  wp m s Q ->
  let '(log, x, _, _) := play A c d s in mrun m log /\ Q (mfold m log) x.
Proof.
  intros St s. induction s as [x|e k IH|f k IH|f k IH|f k IH]; intros m Q A c d H; simpl in *.
  - split; [exact I|exact H].
  - destruct H as [Hok H]. specialize (IH _ _ A c d H).
    destruct (play A c d k) as [[[log x] c'] d']. destruct IH as [Hr HQ].
    split; [split; assumption|exact HQ].
  - destruct (H (clock_answer A c)) as [Hok H']. specialize (IH _ _ _ A (S c) d H').
    destruct (play A (S c) d (k (clock_answer A c))) as [[[log x] c'] d'].
    destruct IH as [Hr HQ]. split; [split; assumption|exact HQ].
  - destruct (H (draw_answer A d)) as [Hok H']. specialize (IH _ _ _ A c (S d) H').
    destruct (play A c (S d) (k (draw_answer A d))) as [[[log x] c'] d'].
    destruct IH as [Hr HQ]. split; [split; assumption|exact HQ].
  - destruct (H (register_answer A f)) as [Hok H']. specialize (IH _ _ _ A c d H').
    destruct (play A c d (k (register_answer A f))) as [[[log x] c'] d'].
    destruct IH as [Hr HQ]. split; [split; assumption|exact HQ].
Qed.

Lemma rev3_mok_task : forall m t, mok m (LTask t).
Proof.
  intros m t. unfold mok. simpl. repeat split; intros; discriminate.
Qed.

(** A runtime whose every task keeps an invariant of the monitor and its state meets I4, I6,
    I7 and I8. *)
Theorem rev3_meets_of_monitor : forall (R : Runtime) (Inv : Mon -> rstate R -> Prop),
  (forall p seed, Inv m0 (init R p seed)) ->
  (forall m s t, Inv m s -> wp (mnext m (LTask t)) (run_task R s t) Inv) ->
  I4 R /\ I6 R /\ I7 R /\ I8 R.
Proof.
  intros R Inv Hinit Hstep.
  assert (Hdrive : forall ts A c d s m, Inv m s -> mrun m (fst (drive R A c d s ts))).
  { induction ts as [|t ts IH]; intros A c d s m Hinv; simpl; [exact I|].
    pose proof (rev3_wp_play _ _ _ _ A c d (Hstep m s t Hinv)) as Hp.
    destruct (play A c d (run_task R s t)) as [[[log s'] c'] d'].
    destruct Hp as [Hr HQ].
    specialize (IH A c' d' s' _ HQ).
    destruct (drive R A c' d' s' ts) as [log' s'']. simpl in *.
    split; [apply rev3_mok_task|]. apply rev3_mrun_app. split; assumption. }
  assert (H : forall p seed A ts, mrun m0 (fst (drive R A 0 0 (init R p seed) ts))).
  { intros. apply Hdrive. apply Hinit. }
  pose proof (fun p seed A ts => rev3_mrun_props _ (H p seed A ts)) as HP.
  unfold I4, I6, I7, I8. split; [split|split; [|split]].
  - intros p seed A ts pre f tok op post Heq.
    exact (proj1 (HP p seed A ts) _ _ _ _ _ Heq).
  - intros p seed A ts. exact (proj1 (proj2 (HP p seed A ts))).
  - intros p seed A ts. split; [exact (proj1 (proj2 (proj2 (HP p seed A ts))))|].
    exact (rev3_mrun_root_after _ (H p seed A ts)).
  - intros p seed A ts. exact (proj1 (proj2 (proj2 (proj2 (HP p seed A ts))))).
  - intros p seed A ts pre e post f Heq Hf.
    exact (proj2 (proj2 (proj2 (proj2 (HP p seed A ts)))) _ _ _ _ Heq Hf).
Qed.

(** I1 for a runtime whose equivalence is equality. *)
Lemma rev3_script_rel_refl : forall St (s : Script St), script_rel eq s s.
Proof.
  intros St s. induction s; constructor; auto.
Qed.

Theorem rev3_i1_of_eq : forall R, (forall s1 s2, requiv R s1 s2 <-> s1 = s2) -> I1 R.
Proof.
  intros R Heq. unfold I1. repeat split.
  - intros s. apply Heq. reflexivity.
  - intros s1 s2 H. apply Heq. apply Heq in H. symmetry. exact H.
  - intros s1 s2 s3 H1 H2. apply Heq. apply Heq in H1. apply Heq in H2. congruence.
  - intros s1 s2 t H. apply Heq in H. subst.
    assert (Hr : forall s : Script (rstate R), script_rel (requiv R) s s).
    { intros s. induction s; constructor; auto. apply Heq. reflexivity. }
    apply Hr.
Qed.

(** ** When an entry is accepted *)

Definition no_pend (m : Mon) (f : FiberId) : Prop := forall tok, ~ In (f, tok) (mpend m).

Lemma rev3_mok_register : forall m f b,
  ~ In f (mreg m) -> ~ In f (mex m) -> no_pend m f -> mok m (LRegister f b).
Proof.
  intros m f b Hr He Hp. unfold mok. split; [|split; [|split; [|split]]].
  - intros g Hg. simpl in Hg. injection Hg as <-. split; [right; exists b; reflexivity|].
    split; [exact He|]. intros tok Hin. destruct (Hp tok Hin).
  - intros g b' Hg. injection Hg as <- _. exact Hr.
  - intros; discriminate.
  - intros; discriminate.
  - intros; discriminate.
Qed.

Lemma rev3_mok_fiber : forall m f e,
  entry_fiber e = Some f ->
  (match e with LRegister _ _ | LEvent (EvStart _ _ _) | LEvent (EvRelease _ _) => False
   | _ => True end) ->
  In f (mreg m) -> ~ In f (mex m) -> no_pend m f -> mok m e.
Proof.
  intros m f e Hf Hk Hr He Hp. unfold mok. split; [|split; [|split; [|split]]].
  - intros g Hg. rewrite Hf in Hg. injection Hg as <-.
    split; [left; exact Hr|]. split; [exact He|]. intros tok Hin. destruct (Hp tok Hin).
  - intros g b ->. destruct Hk.
  - intros g tok op ->. destruct Hk.
  - intros r ->. discriminate.
  - intros r ->. discriminate.
Qed.

Lemma rev3_mok_start : forall m f tok op,
  In f (mreg m) -> ~ In f (mex m) -> no_pend m f -> ~ In tok (mtoks m) ->
  mok m (LEvent (EvStart f tok op)).
Proof.
  intros m f tok op Hr He Hp Ht. unfold mok. split; [|split; [|split; [|split]]].
  - intros g Hg. simpl in Hg. injection Hg as <-.
    split; [left; exact Hr|]. split; [exact He|]. intros t Hin. destruct (Hp t Hin).
  - intros; discriminate.
  - intros g t o Hg. injection Hg as <- <- <-. exact Ht.
  - intros; discriminate.
  - intros; discriminate.
Qed.

Lemma rev3_mok_release : forall m f tok,
  In f (mreg m) -> ~ In f (mex m) -> (forall t, In (f, t) (mpend m) -> t = tok) ->
  mok m (LEvent (EvRelease f tok)).
Proof.
  intros m f tok Hr He Hp. unfold mok. split; [|split; [|split; [|split]]].
  - intros g Hg. simpl in Hg. injection Hg as <-.
    split; [left; exact Hr|]. split; [exact He|]. intros t Hin.
    rewrite (Hp t Hin). simpl. rewrite !Nat.eqb_refl. reflexivity.
  - intros; discriminate.
  - intros; discriminate.
  - intros; discriminate.
  - intros; discriminate.
Qed.

Lemma rev3_mok_queue : forall m p t, mok m (LEvent (EvQueue p t)).
Proof.
  intros m p t. unfold mok. repeat split; intros; discriminate.
Qed.

Lemma rev3_mok_root : forall m r f, mrx m = false -> mfirst m = Some f -> In f (mex m) ->
  mok m (LEvent (EvRootExit r)).
Proof.
  intros m r f Hx Hf He. unfold mok. split; [|split; [|split; [|split]]]; intros; try discriminate.
  - exact Hx.
  - exists f. split; assumption.
Qed.

(** After a release of [tok] by [f], no await of [f] by [tok] is open. *)
Lemma rev3_pend_release : forall m f tok g t,
  In (g, t) (mpend (mnext m (LEvent (EvRelease f tok)))) ->
  In (g, t) (mpend m) /\ ~ (g = f /\ t = tok).
Proof.
  intros m f tok g t H. simpl in H. apply filter_In in H. destruct H as [H Hs].
  split; [exact H|]. intros [-> ->]. unfold still_open in Hs. simpl in Hs.
  rewrite !Nat.eqb_refl in Hs. discriminate.
Qed.

Lemma rev3_pend_task : forall m t g tok,
  In (g, tok) (mpend (mnext m (LTask t))) -> In (g, tok) (mpend m) /\ ends_await g tok (LTask t) = false.
Proof.
  intros m t g tok H. simpl in H. apply filter_In in H. destruct H as [H Hs].
  split; [exact H|]. unfold still_open in Hs. cbn [fst snd] in Hs.
  destruct (ends_await g tok (LTask t)); [discriminate|reflexivity].
Qed.

(** Entries that are not a start, a release, a register or a task leave the open awaits
    as they are. *)
Lemma rev3_pend_other : forall m e g tok,
  (match e with LRegister _ _ | LEvent (EvStart _ _ _) | LEvent (EvRelease _ _) | LTask _ => False
   | _ => True end) ->
  (In (g, tok) (mpend (mnext m e)) <-> In (g, tok) (mpend m)).
Proof.
  intros m e g tok Hk.
  assert (Hf : filter (still_open e) (mpend m) = mpend m).
  { apply forallb_filter_id. apply forallb_forall. intros [g' t'] _. unfold still_open.
    destruct e as [|[]| | |]; try destruct Hk; reflexivity. }
  destruct e as [|[]| | |]; try destruct Hk; simpl; rewrite Hf; tauto.
Qed.
