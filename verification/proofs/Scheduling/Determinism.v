(** * S3, violations are trace events, and S10, random replay.

    Both follow from S1 for one environment and two arrival schedules: the two traces are
    compatible, so they agree at every position both reach, and the draws in them are
    compatible too. *)

From Coq Require Import List ZArith Bool Arith.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model Executor Statements ExecutorLemmas Arrival.
Import ListNotations.

(** Two compatible lists agree at every position both have. *)
Lemma compatible_nth : forall {X} (l1 l2 : list X) i x,
  compatible l1 l2 -> nth_error l1 i = Some x -> (i < length l2)%nat ->
  nth_error l2 i = Some x.
Proof.
  intros X l1 l2 i x [[r ->]|[r ->]] Hx Hi.
  - rewrite nth_error_app1; [exact Hx|]. apply nth_error_Some. rewrite Hx. discriminate.
  - rewrite nth_error_app1 in Hx; [exact Hx|exact Hi].
Qed.

Theorem s3 : S3.
Proof.
  intros P E A1 A2 n1 n2 i v _ Hv Hi.
  apply (compatible_nth (run P E A1 n1)); [|exact Hv|exact Hi].
  apply s1_any_schedule; [apply same_values_refl|reflexivity].
Qed.

Lemma draws_of_prefix : forall l1 l2, prefix l1 l2 -> prefix (draws_of l1) (draws_of l2).
Proof.
  intros l1 l2 [r ->]. exists (draws_of r). unfold draws_of. apply flat_map_app.
Qed.

Theorem s10 : S10.
Proof.
  intros P E A1 A2 n1 n2 _.
  destruct (s1_any_schedule P E E A1 A2 n1 n2 (same_values_refl E) eq_refl) as [H|H];
    [left|right]; apply draws_of_prefix; exact H.
Qed.
