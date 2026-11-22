(** * Only a start event records a start.

    The first part of [time_fresh_tokens]: the tokens the executor's trace reports started are
    a subsequence of the tokens the runtime's events report started, in the order the
    executor ran its tasks. A step that runs no task records no start; a task records one
    start for each start event it reports while the attempt is not done. *)

From Coq Require Import List ZArith Bool Arith Lia.
From Durable Require Import Runtime Exec Rev3 Statements TimeBase TimeStep.
Import ListNotations.
Open Scope Z_scope.

(** ** Subsequences *)

Inductive time_subseq : list Token -> list Token -> Prop :=
| time_subseq_nil : time_subseq [] []
| time_subseq_skip : forall a l l', time_subseq l l' -> time_subseq l (a :: l')
| time_subseq_take : forall a l l', time_subseq l l' -> time_subseq (a :: l) (a :: l').

Lemma time_subseq_refl : forall l, time_subseq l l.
Proof. induction l; [constructor|apply time_subseq_take; auto]. Qed.

Lemma time_subseq_nil_l : forall l, time_subseq [] l.
Proof. induction l; [constructor|apply time_subseq_skip; auto]. Qed.

Lemma time_subseq_app : forall a a' b b',
  time_subseq a a' -> time_subseq b b' -> time_subseq (a ++ b) (a' ++ b').
Proof.
  intros a a' b b' H1 H2. induction H1; cbn;
    [exact H2|apply time_subseq_skip; auto|apply time_subseq_take; auto].
Qed.

Lemma time_subseq_in : forall l l' x, time_subseq l l' -> In x l -> In x l'.
Proof.
  intros l l' x H. induction H; cbn; intros Hi; [exact Hi|right; auto|].
  destruct Hi as [<-|Hi]; [left; reflexivity|right; auto].
Qed.

Lemma time_subseq_nodup : forall l l', time_subseq l l' -> NoDup l' -> NoDup l.
Proof.
  intros l l' H. induction H; intros N.
  - constructor.
  - inversion N; subst. auto.
  - inversion N; subst. constructor; [|auto]. intros Hi. apply H2.
    eapply time_subseq_in; eauto.
Qed.

Lemma time_subseq_trans : forall a b c, time_subseq a b -> time_subseq b c -> time_subseq a c.
Proof.
  intros a b c H1 H2. revert a H1. induction H2; intros a0 H1.
  - inversion H1; subst. constructor.
  - apply time_subseq_skip. auto.
  - inversion H1; subst; [apply time_subseq_skip; auto|apply time_subseq_take; auto].
Qed.

(** ** Growth without a start *)

Definition time_nostart (x x' : XState) : Prop :=
  exists r, trace x' = trace x ++ r /\ time_stoks r = [].

Lemma time_nostart_refl : forall x, time_nostart x x.
Proof. intros x. exists []. rewrite app_nil_r. auto. Qed.

Lemma time_nostart_same : forall x x', trace x' = trace x -> time_nostart x x'.
Proof. intros x x' H. exists []. rewrite H, app_nil_r. auto. Qed.

Lemma time_nostart_trans : forall x y z,
  time_nostart x y -> time_nostart y z -> time_nostart x z.
Proof.
  intros x y z [r1 [H1 S1]] [r2 [H2 S2]]. exists (r1 ++ r2).
  rewrite H2, H1, app_assoc, time_stoks_app, S1, S2. auto.
Qed.

Lemma time_nostart_emit : forall x a,
  (forall f tok op, a <> AStart f tok op) -> time_nostart x (emit x a).
Proof.
  intros x a H. exists [a]. split; [reflexivity|]. destruct a; cbn; auto.
  exfalso. eapply H. reflexivity.
Qed.

Lemma time_nostart_close : forall x c, time_nostart x (close x c).
Proof. intros. apply time_nostart_same. apply (time_close_fields x c). Qed.

Lemma time_nostart_violate : forall x v, time_nostart x (violate x v).
Proof.
  intros x v. unfold violate. destruct (violated x); [apply time_nostart_refl|].
  eapply time_nostart_trans; [apply (time_nostart_emit x (AViolation v)); discriminate|].
  eapply time_nostart_trans; [|apply time_nostart_close]. apply time_nostart_same.
  reflexivity.
Qed.

Lemma time_nostart_finish : forall x v, time_nostart x (finish x v).
Proof. intros. exists [AExit v]. auto. Qed.

Lemma time_nostart_issue : forall I x k o s, time_nostart x (issue I x k o s).
Proof.
  intros. destruct (time_issue_cases I x k o s) as [-> | ->]; [apply time_nostart_finish|].
  exists [ACommand (next_cmd x) k o]. auto.
Qed.

Lemma time_nostart_issue_op : forall I x f tok op, time_nostart x (issue_op I x f tok op).
Proof.
  intros. unfold issue_op. destruct op; [apply time_nostart_issue|].
  destruct (match d with Millis m => split m | Forever => (max_chunk, Endless) end).
  apply time_nostart_issue.
Qed.

Ltac time_ns :=
  repeat (cbn [enqueue issue_sample on_foreign on_cancel on_notify after_sample at_boundary
               at_boundary_sub] in *;
          match goal with
          | |- time_nostart _ _ => first
              [ apply time_nostart_refl
              | apply time_nostart_same; reflexivity
              | apply time_nostart_violate
              | apply time_nostart_finish
              | apply time_nostart_issue
              | apply time_nostart_issue_op
              | apply time_nostart_close
              | match goal with |- context [match ?e with _ => _ end] => destruct e end ]
          end).

Lemma time_nostart_release : forall x f tok, time_nostart x (on_release x f tok).
Proof.
  intros. apply time_nostart_same. unfold on_release.
  repeat (cbn; match goal with |- context [match ?e with _ => _ end] => destruct e end);
    reflexivity.
Qed.

Lemma time_nostart_after : forall I x after, time_nostart x (after_sample I x after).
Proof.
  intros. destruct after; cbn [after_sample]; unfold enqueue;
    try (apply time_nostart_same; reflexivity).
  destruct (link_of rest) as [[? ?]|]; [apply time_nostart_issue|].
  apply time_nostart_same; reflexivity.
Qed.

Lemma time_nostart_apply : forall I x c v after,
  time_nostart x (let x1 := apply_sample x c v after in
                  match phase x1 with POpen => after_sample I x1 after | _ => x1 end).
Proof.
  intros. cbv zeta.
  assert (H : time_nostart x (apply_sample x c v after)).
  { unfold apply_sample.
    match goal with |- context [if ?b then _ else _] => destruct b end;
      [apply time_nostart_violate|].
    eexists. split; [reflexivity|]. reflexivity. }
  destruct (phase (apply_sample x c v after)); [|exact H..].
  eapply time_nostart_trans; [exact H|apply time_nostart_after].
Qed.

Lemma time_nostart_cancel : forall I x s, time_nostart x (on_cancel I x s).
Proof.
  intros I x s. destruct s as [c f tok op k rest|c []|c]; cbn [on_cancel issue_sample];
    first [apply time_nostart_issue | apply time_nostart_same; reflexivity
          | eapply time_nostart_trans; [|apply time_nostart_issue];
            apply time_nostart_same; reflexivity].
Qed.

Lemma time_nostart_notify : forall I x s r, time_nostart x (on_notify I x s r).
Proof.
  intros I x s r. destruct s as [c f tok op k rest|c after|c];
    [destruct r; [destruct op|..]|destruct after, r|destruct r];
    cbn [on_notify issue_sample];
    try first [apply time_nostart_issue | apply time_nostart_violate
          | apply time_nostart_same; reflexivity | apply time_nostart_apply].
  all: destruct op; apply time_nostart_refl.
Qed.

Lemma time_nostart_boundary : forall I Sch x x',
  at_boundary I Sch x = Some x' -> time_nostart x x'.
Proof.
  intros I Sch x x' E. unfold at_boundary in E.
  destruct (phase x); try discriminate.
  2: { inversion E; subst. apply time_nostart_finish. }
  destruct (held x), (waiter x) as [[[f tok] op]|].
  1: { inversion E; subst. apply time_nostart_same. reflexivity. }
  all: destruct (sub x) as [s|];
    [|inversion E; subst;
      first [apply time_nostart_violate
            |eapply time_nostart_trans; [|apply time_nostart_issue_op];
             apply time_nostart_same; reflexivity]].
  all: unfold at_boundary_sub in E;
    destruct (arrived Sch (micro x) <=? cursor x)%nat; [discriminate|];
    destruct (nth_error (entries I) (cursor x)) as [[c r|]|]; try discriminate;
    [destruct (Nat.eqb c (sub_cmd s));
      [|destruct (c <? next_cmd x)%nat; inversion E; subst;
        apply time_nostart_same; reflexivity]
    |].
  all: inversion E; subst; clear E.
  all: eapply time_nostart_trans;
    [apply (time_nostart_same x (set_cursor x (S (cursor x)))); reflexivity|].
  all: first [apply time_nostart_notify | apply time_nostart_cancel].
Qed.

Lemma time_nostart_cut : forall x k, time_nostart x (on_cut x k).
Proof.
  intros x k. unfold on_cut.
  eapply time_nostart_trans; [apply (time_nostart_emit x (ACut k)); discriminate|].
  destruct k; [apply time_nostart_close|apply time_nostart_close|].
  apply time_nostart_same. reflexivity.
Qed.

Lemma time_nostart_foreign : forall x fi, time_nostart x (on_foreign x fi).
Proof.
  intros x fi. destruct fi; cbn [on_foreign];
    first [apply time_nostart_violate | apply time_nostart_refl].
Qed.

(** ** Events with at most one start *)

(** [x'] extends [x] by actions whose starts are a subsequence of [S]. *)
Definition time_grows_sub (x x' : XState) (S : list Token) : Prop :=
  exists r, trace x' = trace x ++ r /\ time_subseq (time_stoks r) S.

Lemma time_grows_sub_nostart : forall x x' S, time_nostart x x' -> time_grows_sub x x' S.
Proof.
  intros x x' S [r [T E]]. exists r. split; [exact T|]. rewrite E. apply time_subseq_nil_l.
Qed.

Lemma time_grows_sub_trans : forall x y z S1 S2,
  time_grows_sub x y S1 -> time_grows_sub y z S2 -> time_grows_sub x z (S1 ++ S2).
Proof.
  intros x y z S1 S2 [r1 [H1 E1]] [r2 [H2 E2]]. exists (r1 ++ r2).
  rewrite H2, H1, app_assoc, time_stoks_app. split; [reflexivity|].
  apply time_subseq_app; assumption.
Qed.

Lemma time_grows_sub_event : forall I x e,
  time_grows_sub x (on_event I x e) (start_tokens [LEvent e]).
Proof.
  intros I x e. unfold on_event. destruct (phase x) eqn:Ph;
    try (apply time_grows_sub_nostart; apply time_nostart_refl).
  all: destruct e as [f tok op|f tok|pr t|f|r]; cbn [start_tokens flat_map].
  all: try (apply time_grows_sub_nostart;
    first [apply time_nostart_release
          | destruct (Nat.eqb pr 0); [apply time_nostart_same; reflexivity
                                     |apply time_nostart_violate]
          | apply time_nostart_same; reflexivity
          | destruct (root_exit x); [apply time_nostart_violate|];
            eapply time_nostart_trans; [|apply time_nostart_close];
            apply time_nostart_same; reflexivity]).
  all: unfold on_start; rewrite Ph.
  - replace [tok] with ([tok] ++ []) by reflexivity.
    apply (time_grows_sub_trans x (emit x (AStart f tok op)) _ [tok] []).
    { exists [AStart f tok op]. split; [reflexivity|apply time_subseq_refl]. }
    apply time_grows_sub_nostart.
    destruct (zero_sleep op); [apply time_nostart_same; reflexivity|].
    destruct (awaiter (emit x (AStart f tok op))); [apply time_nostart_violate|].
    destruct (held (emit x (AStart f tok op))); [apply time_nostart_same; reflexivity|].
    destruct (slot_held (emit x (AStart f tok op))); [apply time_nostart_same; reflexivity|].
    eapply time_nostart_trans; [|apply time_nostart_issue_op].
    apply time_nostart_same. reflexivity.
  - exists [AStart f tok op]. split; [reflexivity|apply time_subseq_refl].
Qed.
