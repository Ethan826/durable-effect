(** * [time_fresh_tokens] from [Meets].

    [drive], given the answers the executor gave, reproduces the executor's log of its
    tasks. The proof runs [play] and [interp] side by side; at a registration, the answer is
    the one the fiber got the first time, and a second registration of a fiber would break
    I7 for that very [drive]. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Rev3 Statements TimeBase TimeStep TimeFresh1
  TimeFresh2.
Import ListNotations.
Open Scope Z_scope.

Definition time_clocks (L : list LogEntry) : list Z :=
  flat_map (fun e => match e with LClock _ l => [l] | _ => [] end) L.

Definition time_draws (L : list LogEntry) : list nat :=
  flat_map (fun e => match e with LDraw _ r => [r] | _ => [] end) L.

Lemma time_started_app : forall a b, started (a ++ b) = started a ++ started b.
Proof. intros. unfold started. apply flat_map_app. Qed.

Lemma time_nodup_started : forall X f b Y,
  NoDup (started (X ++ LRegister f b :: Y)) -> ~ In f (started X).
Proof.
  intros X f b Y N Hi. rewrite time_started_app in N. cbn in N.
  apply NoDup_remove_2 in N. apply N. apply in_or_app. left. exact Hi.
Qed.

(** ** One script *)

Lemma time_play_ilog : forall A I X (s : Script X) x c d Pre,
  (forall i v, nth_error (time_clocks (time_ilog I x s)) i = Some v ->
     clock_answer A (c + i)%nat = v) ->
  (forall i v, nth_error (time_draws (time_ilog I x s)) i = Some v ->
     draw_answer A (d + i)%nat = v) ->
  (forall P f b Q, time_ilog I x s = P ++ LRegister f b :: Q ->
     ~ In f (started (Pre ++ P)) -> register_answer A f = b) ->
  (forall P f b Q, fst (fst (fst (play A c d s))) = P ++ LRegister f b :: Q ->
     ~ In f (started (Pre ++ P))) ->
  play A c d s = (time_ilog I x s, snd (interp I x s),
                  (c + length (time_clocks (time_ilog I x s)))%nat,
                  (d + length (time_draws (time_ilog I x s)))%nat).
Proof.
  intros A I X s. induction s as [r|e k IH|f k IH|f k IH|f k IH];
    intros x c d Pre Hc Hd Hr Hp; cbn [play time_ilog interp] in *.
  - cbn. rewrite !Nat.add_0_r. reflexivity.
  - destruct (play A c d k) as [[[lg x'] c'] d'] eqn:E.
    pose proof (IH (on_event I x e) c d (Pre ++ [LEvent e])) as H. rewrite E in H.
    match type of H with _ -> _ -> _ -> _ -> ?q => cut q end;
      [intros H2; injection H2 as -> -> -> ->; reflexivity|apply H].
    + exact Hc.
    + exact Hd.
    + intros P g b Q H1 N. apply (Hr (LEvent e :: P) g b Q); [rewrite H1; reflexivity|].
      rewrite <- app_assoc in N. exact N.
    + intros P g b Q H'. cbn in H'. rewrite <- app_assoc.
      apply (Hp (LEvent e :: P) g b Q). cbn. rewrite ?E, H'. reflexivity.
  - assert (C0 : clock_answer A c = logical x)
      by (rewrite <- (Nat.add_0_r c); apply Hc; reflexivity).
    rewrite C0 in *.
    destruct (play A (S c) d (k (logical x))) as [[[lg x'] c'] d'] eqn:E.
    pose proof (IH (logical x) (match phase x with PDone => x | _ => emit x (AClock f (logical x)) end) (S c) d (Pre ++ [LClock f (logical x)])) as H.
    rewrite E in H.
    match type of H with _ -> _ -> _ -> _ -> ?q => cut q end;
      [intros H2; injection H2 as -> -> -> ->; cbn [length time_clocks time_draws flat_map app];
       rewrite ?Nat.add_succ_r; reflexivity|apply H].
    + intros i v H1. replace (S c + i)%nat with (c + S i)%nat by lia. apply Hc. exact H1.
    + exact Hd.
    + intros P g b Q H1 N. apply (Hr (LClock f (logical x) :: P) g b Q);
        [rewrite H1; reflexivity|].
      rewrite <- app_assoc in N. exact N.
    + intros P g b Q H'. cbn in H'. rewrite <- app_assoc.
      apply (Hp (LClock f (logical x) :: P) g b Q). cbn. rewrite ?E, H'. reflexivity.
  - assert (D0 : draw_answer A d = stream I (draws x))
      by (rewrite <- (Nat.add_0_r d); apply Hd; reflexivity).
    rewrite D0 in *.
    destruct (play A c (S d) (k (stream I (draws x)))) as [[[lg x'] c'] d'] eqn:E.
    pose proof (IH (stream I (draws x)) (match phase x with
      | PDone => x
      | _ => emit (set_draws x (S (draws x))) (ADraw f (stream I (draws x))) end) c (S d) (Pre ++ [LDraw f (stream I (draws x))]))
      as H. rewrite E in H.
    match type of H with _ -> _ -> _ -> _ -> ?q => cut q end;
      [intros H2; injection H2 as -> -> -> ->; cbn [length time_clocks time_draws flat_map app];
       rewrite ?Nat.add_succ_r; reflexivity|apply H].
    + exact Hc.
    + intros i v H1. replace (S d + i)%nat with (d + S i)%nat by lia. apply Hd. exact H1.
    + intros P g b Q H1 N. apply (Hr (LDraw f (stream I (draws x)) :: P) g b Q);
        [rewrite H1; reflexivity|].
      rewrite <- app_assoc in N. exact N.
    + intros P g b Q H'. cbn in H'. rewrite <- app_assoc.
      apply (Hp (LDraw f (stream I (draws x)) :: P) g b Q). cbn. rewrite ?E, H'. reflexivity.
  - set (cl := match phase x with PClosing _ => true | _ => false end) in *.
    assert (R0 : register_answer A f = cl).
    { apply (Hr [] f cl _ eq_refl). rewrite app_nil_r.
      destruct (play A c d (k (register_answer A f))) as [[[lg x'] c'] d'] eqn:E.
      rewrite <- (app_nil_r Pre) at 1.
      apply (Hp [] f (register_answer A f) lg). reflexivity. }
    rewrite R0 in *.
    destruct (play A c d (k cl)) as [[[lg x'] c'] d'] eqn:E.
    pose proof (IH cl (set_live x (live x ++ [f])) c d (Pre ++ [LRegister f cl])) as H. rewrite E in H.
    match type of H with _ -> _ -> _ -> _ -> ?q => cut q end;
      [intros H2; injection H2 as -> -> -> ->; reflexivity|apply H].
    + exact Hc.
    + exact Hd.
    + intros P g b Q H1 N. apply (Hr (LRegister f cl :: P) g b Q);
        [rewrite H1; reflexivity|].
      rewrite <- app_assoc in N. exact N.
    + intros P g b Q H'. cbn in H'. rewrite <- app_assoc.
      apply (Hp (LRegister f cl :: P) g b Q). cbn. rewrite ?E, H'. reflexivity.
Qed.

(** ** All the tasks of an attempt *)

Lemma time_clocks_app : forall a b, time_clocks (a ++ b) = time_clocks a ++ time_clocks b.
Proof. intros. unfold time_clocks. apply flat_map_app. Qed.

Lemma time_draws_app : forall a b, time_draws (a ++ b) = time_draws a ++ time_draws b.
Proof. intros. unfold time_draws. apply flat_map_app. Qed.

Lemma time_drive_log : forall R A I Sch n s c d Pre,
  (forall i v, nth_error (time_clocks (time_log R I Sch n s)) i = Some v ->
     clock_answer A (c + i)%nat = v) ->
  (forall i v, nth_error (time_draws (time_log R I Sch n s)) i = Some v ->
     draw_answer A (d + i)%nat = v) ->
  (forall P f b Q, time_log R I Sch n s = P ++ LRegister f b :: Q ->
     ~ In f (started (Pre ++ P)) -> register_answer A f = b) ->
  NoDup (started (Pre ++ fst (drive R A c d (rs s) (time_tasks R I Sch n s)))) ->
  fst (drive R A c d (rs s) (time_tasks R I Sch n s)) = time_log R I Sch n s.
Proof.
  intros R A I Sch n. induction n as [|n IH]; intros s c d Pre Hc Hd Hr N;
    [reflexivity|].
  cbn [time_tasks time_log] in *. pose proof (time_step_cases R I Sch s) as C.
  unfold time_step_log in *.
  destruct (time_step_task R I Sch s) as [[t rest]|].
  2: { destruct C as [_ Rs]. cbn [app] in *. rewrite <- Rs in *. apply (IH _ _ _ Pre); assumption. }
  destruct C as [_ [_ Rs]]. cbn [app drive] in *.
  set (L1 := time_ilog I (time_x2 (xs s) t rest) (run_task R (rs s) t)) in *.
  destruct (play A c d (run_task R (rs s) t)) as [[[lg s'] c'] d'] eqn:E.
  destruct (drive R A c' d' s' (time_tasks R I Sch n (step R I Sch s))) as [lg' s''] eqn:E2.
  cbn [fst] in *.
  assert (Hpl : play A c d (run_task R (rs s) t) =
    (L1, snd (interp I (time_x2 (xs s) t rest) (run_task R (rs s) t)),
     (c + length (time_clocks L1))%nat, (d + length (time_draws L1))%nat)).
  { apply (time_play_ilog A I _ _ _ c d (Pre ++ [LTask t])).
    - intros i v H. apply Hc. cbn [time_clocks flat_map app].
      change (nth_error (time_clocks (L1 ++ time_log R I Sch n (step R I Sch s))) i = Some v).
      rewrite time_clocks_app, nth_error_app1; [exact H|].
      fold L1 in H. apply nth_error_Some. congruence.
    - intros i v H. apply Hd.
      change (nth_error (time_draws (L1 ++ time_log R I Sch n (step R I Sch s))) i = Some v).
      rewrite time_draws_app, nth_error_app1; [exact H|].
      fold L1 in H. apply nth_error_Some. congruence.
    - intros P f b Q H Ni. apply (Hr (LTask t :: P) f b (Q ++ time_log R I Sch n (step R I Sch s))).
      + fold L1 in H. rewrite H. rewrite <- app_assoc. reflexivity.
      + rewrite <- app_assoc in Ni. exact Ni.
    - intros P f b Q H. rewrite E in H. cbn in H. subst lg.
      rewrite <- app_assoc. cbn [app].
      apply (time_nodup_started _ f b (Q ++ lg')).
      replace ((Pre ++ LTask t :: P) ++ LRegister f b :: Q ++ lg') with
        (Pre ++ LTask t :: (P ++ LRegister f b :: Q) ++ lg')
        by (rewrite <- !app_assoc; reflexivity).
      exact N. }
  rewrite E in Hpl. injection Hpl as -> -> -> ->.
  f_equal. f_equal.
  assert (Ed : fst (drive R A (c + length (time_clocks L1))%nat (d + length (time_draws L1))%nat
             (rs (step R I Sch s)) (time_tasks R I Sch n (step R I Sch s))) = lg')
    by (rewrite Rs, E2; reflexivity).
  rewrite <- Ed. apply (IH _ _ _ (Pre ++ LTask t :: L1)).
  - intros i v H. rewrite <- Nat.add_assoc. apply Hc. cbn [time_clocks flat_map app].
    change (nth_error (time_clocks (L1 ++ time_log R I Sch n (step R I Sch s)))
              (length (time_clocks L1) + i) = Some v).
    rewrite time_clocks_app, nth_error_app2 by lia.
    replace (length (time_clocks L1) + i - length (time_clocks L1))%nat with i by lia.
    exact H.
  - intros i v H. rewrite <- Nat.add_assoc. apply Hd.
    change (nth_error (time_draws (L1 ++ time_log R I Sch n (step R I Sch s)))
              (length (time_draws L1) + i) = Some v).
    rewrite time_draws_app, nth_error_app2 by lia.
    replace (length (time_draws L1) + i - length (time_draws L1))%nat with i by lia.
    exact H.
  - intros P f b Q H Ni. apply (Hr (LTask t :: L1 ++ P) f b Q).
    + rewrite H. cbn [app]. rewrite app_assoc. reflexivity.
    + rewrite <- app_assoc in Ni. exact Ni.
  - rewrite Ed. rewrite <- app_assoc. exact N.
Qed.

(** ** The answers the executor gave *)

Fixpoint time_first_reg (f : FiberId) (L : list LogEntry) : bool :=
  match L with
  | [] => false
  | LRegister g b :: r => if Nat.eqb f g then b else time_first_reg f r
  | _ :: r => time_first_reg f r
  end.

Lemma time_first_reg_spec : forall f b P Q,
  ~ In f (started P) -> time_first_reg f (P ++ LRegister f b :: Q) = b.
Proof.
  intros f b P Q. induction P as [|e P IH]; intros N.
  - cbn. rewrite Nat.eqb_refl. reflexivity.
  - destruct e; cbn in N |- *; try (apply IH; exact N).
    destruct (Nat.eqb f f0) eqn:E.
    + apply Nat.eqb_eq in E. subst. exfalso. apply N. left. reflexivity.
    + apply IH. intros Hi. apply N. right. exact Hi.
Qed.

Definition time_answers (L : list LogEntry) : Answers :=
  {| clock_answer := fun i => nth i (time_clocks L) 0;
     draw_answer := fun i => nth i (time_draws L) 0%nat;
     register_answer := fun f => time_first_reg f L |}.

Lemma time_initial_stoks : forall R p I, time_stoks (trace (xs (initial R p I))) = [].
Proof.
  intros R p I. unfold initial, issue_sample. tsimp.
  match goal with |- context [issue ?I ?y ?k ?o ?s] =>
    destruct (time_issue_cases I y k o s) as [-> | ->] end; reflexivity.
Qed.

(** I4's second half, carried to the executor's trace. *)
Theorem time_fresh_tokens_hold : time_fresh_tokens.
Proof.
  intros R HR p I Sch n. destruct HR as [_ [[_ I4b] [_ [I7 _]]]].
  set (L := time_log R I Sch n (initial R p I)).
  set (A := time_answers L).
  set (ts := time_tasks R I Sch n (initial R p I)).
  assert (D : fst (drive R A 0 0 (rs (initial R p I)) ts) = L).
  { apply (time_drive_log R A I Sch n (initial R p I) 0 0 []).
    - intros i v H. cbn. apply nth_error_nth. exact H.
    - intros i v H. cbn. apply nth_error_nth. exact H.
    - intros P f b Q H Ni. cbn. fold L in H. rewrite H.
      apply time_first_reg_spec. exact Ni.
    - cbn [app]. apply (I7 p (seed I) A ts). }
  pose proof (I4b p (seed I) A ts) as N. change (init R p (seed I)) with (rs (initial R p I)) in N.
  rewrite D in N.
  destruct (time_run_sub R I Sch n (initial R p I)) as [r [T S]].
  unfold run. rewrite T, time_stoks_app, time_initial_stoks. cbn [app].
  eapply time_subseq_nodup; [exact S|exact N].
Qed.
