(** * Lemmas for S9: running one fiber under revision 4's executor and revision 3's.

    The two executors differ in [run_fiber]'s [Sleep] case and in the step taken when the
    queue is empty and nothing is awaited. A program with one fiber keeps a state with that
    one fiber, of handle 0, whose code, finalizer and pending continuation never fork. While
    that fiber runs, nothing is awaited, so a sleep it starts is never a second await. Then
    the [Sleep] case differs only for a sleep longer than [max_chunk] or infinite, where
    revision 4 starts a chain; [in_common] rules that out. *)

From Coq Require Import List ZArith Bool Arith Lia.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model Executor Statements SingleStepLemmas.
Import ListNotations.
Open Scope Z_scope.

(** ** The single-fiber invariant *)

(** A pending continuation whose every result never forks. *)
Definition pending_ok (p : Pending) : Prop :=
  match p with
  | NoPending => True
  | ResumeOutcome k => forall v, no_forks (k v)
  | ResumeUnit k => forall v, no_forks (k v)
  | ResumeNat k => forall v, no_forks (k v)
  end.

(** The one fiber: handle 0, and nothing it can still run forks. *)
Definition fiber_ok (f : Fiber) : Prop :=
  handle f = 0%nat /\ no_forks (code f) /\ no_forks (fin f) /\ pending_ok (pending f).

(** An awaited operation belongs to the fiber, which is then not ready to run. *)
Definition aw_ok (aw : option Awaited) (f : Fiber) : Prop :=
  match aw with
  | None => True
  | Some a => awaited_handle a = 0%nat /\ status f <> Ready
  end.

(** The invariant on revision 4's reachable states, until the attempt finishes. *)
Definition SF (st : State) : Prop :=
  finished st = None ->
  exists f, fibers st = [f] /\ fiber_ok f /\ aw_ok (awaited st) f.

(** The awaited operation, if any, is not a sleep chain. *)
Definition chain_free (st : State) : Prop :=
  forall h op c r, awaited st = Some (AwaitSleep h op c r) -> r = NoChain.

(** ** Small facts *)

Lemma no_forks_ret : no_forks (Ret tt).
Proof. apply nf_ret with tt. reflexivity. Qed.

(** [no_forks] by cases, stated for any tree so that [destruct] needs no inversion. *)
Lemma no_forks_cases : forall t, no_forks t ->
  (exists r, observe t = RetF r) \/
  (exists u, observe t = TauF u /\ no_forks u) \/
  (exists X (e : FiberE X) k, observe t = VisF e k /\
     (match e with Fork _ _ => False | _ => True end) /\ forall x, no_forks (k x)).
Proof.
  intros t H. destruct H as [r t Ho | t u Ho Hu | X e k t Ho He Hk].
  - left. exists r. exact Ho.
  - right. left. exists u. split; assumption.
  - right. right. exists X, e, k. split; [|split]; assumption.
Qed.

Lemma find_one : forall f, handle f = 0%nat -> find_fiber 0 [f] = Some f.
Proof. intros f H. unfold find_fiber. cbn. rewrite H. reflexivity. Qed.

Lemma find_one_inv : forall f h g, find_fiber h [f] = Some g -> g = f /\ handle f = h.
Proof.
  intros f h g H. unfold find_fiber in H. cbn in H.
  destruct (Nat.eqb (handle f) h) eqn:He; [|discriminate].
  apply Nat.eqb_eq in He. split; congruence.
Qed.

Lemma put_one : forall f g, handle g = handle f -> put_fiber f [g] = [f].
Proof. intros f g H. unfold put_fiber. cbn. rewrite H, Nat.eqb_refl. reflexivity. Qed.

Lemma fiber_ok_set : forall f c s,
  fiber_ok f -> no_forks c -> fiber_ok (set_code f c NoPending s).
Proof. intros f c s (Hh & _ & Hf & _) Hc. repeat split; assumption. Qed.

(** Interrupting a fiber of the one-fiber state, with nothing awaited. *)
Lemma interrupt_one : forall st x t,
  fibers st = [x] -> fiber_ok x -> awaited st = None ->
  exists y, fibers (interrupt_fiber st t) = [y] /\ fiber_ok y /\
    awaited (interrupt_fiber st t) = None.
Proof.
  intros st x t Hf Hx Ha. unfold interrupt_fiber. rewrite Hf.
  destruct (find_fiber t [x]) as [g|] eqn:Hg; [|exists x; rewrite Hf; auto].
  apply find_one_inv in Hg. destruct Hg as [-> Ht].
  destruct (status x); try (exists x; rewrite Hf; auto; fail).
  all: rewrite Ha; cbn [fibers awaited update emit]; rewrite Hf, put_one by exact Ht;
    eexists; split; [reflexivity|]; split; [|reflexivity];
    destruct Hx as (Hh & _ & Hfin & _); repeat split; simpl;
    [congruence | exact Hfin | exact no_forks_ret].
Qed.

Lemma SF_intro : forall st y,
  fibers st = [y] -> fiber_ok y -> aw_ok (awaited st) y -> SF st.
Proof. intros st y Hf Hy Ha _. exists y. auto. Qed.

(** ** Running the one fiber *)

(** The fibers of a state that stores fiber [y] in place of [g]. *)
Local Ltac stored Hfs :=
  cbn [fibers awaited update with_fibers emit]; rewrite Hfs, put_one;
  [reflexivity | cbn; congruence].

(** Nothing awaited after the step. *)
Local Ltac none_awaited Ha := cbn [awaited update with_fibers emit]; rewrite Ha; exact I.

(** The fiber's own operation awaited after the step. *)
Local Ltac own_awaited Hh := cbn; split; [exact Hh | discriminate].

(** Revision 4 runs the one fiber, with nothing awaited, to a state that keeps the invariant,
    and to the state revision 3 reaches unless revision 4 started a sleep chain. *)
Lemma run_fiber_one : forall P E fuel ops st f g,
  fibers st = [g] -> handle g = 0%nat -> fiber_ok f -> awaited st = None ->
  SF (run_fiber policy_v1 P E fuel ops st f) /\
  (chain_free (run_fiber policy_v1 P E fuel ops st f) ->
   run_fiber policy_v1 P E fuel ops st f = run_fiber policy_rev3 P E fuel ops st f).
Proof.
  intros P E fuel. induction fuel as [|fuel IH]; intros ops st f g Hfs Hg Hf Ha;
    cbn [run_fiber]; pose proof Hf as (Hh & Hc & Hfn & _).
  { split; [|reflexivity]. apply SF_intro with f; [stored Hfs | exact Hf | none_awaited Ha]. }
  destruct (finished st) eqn:Hfin; [split; [intros H; congruence | reflexivity]|].
  destruct ops as [|ops].
  { split; [|reflexivity]. apply SF_intro with f; [stored Hfs | exact Hf | none_awaited Ha]. }
  destruct (no_forks_cases _ Hc) as [[r Ho]|[[u [Ho Hu]]|(X & e & k & Ho & He & Hk)]];
    rewrite Ho; cbn beta iota zeta.
  - split; [|reflexivity]. apply SF_intro with (set_code f (Ret tt) NoPending Done);
      [stored Hfs | apply fiber_ok_set; [exact Hf | exact no_forks_ret] | none_awaited Ha].
  - apply IH with g; [exact Hfs | exact Hg | apply fiber_ok_set; assumption | exact Ha].
  - clear Ho. destruct e as [| | kind idx | kind args | d | | target | | r | r v];
      cbn beta iota zeta in He |- *.
    + apply IH with g; [exact Hfs | exact Hg | apply fiber_ok_set; auto | exact Ha].
    + apply IH with g; [exact Hfs | exact Hg | apply fiber_ok_set; auto | exact Ha].
    + contradiction.
    + rewrite Ha. split; [|reflexivity].
      apply SF_intro with (set_code f (code f) (ResumeOutcome k) AwaitingDurable);
        [stored Hfs | repeat split; simpl; assumption | own_awaited Hh].
    + cbn [chunk_long_sleeps policy_v1 policy_rev3]. rewrite Ha.
      destruct d as [ms|].
      * destruct (ms <=? 0) eqn:H0.
        { split; [|reflexivity]. apply SF_intro with (set_code f (k tt) NoPending Ready);
            [stored Hfs | apply fiber_ok_set; auto | none_awaited Ha]. }
        destruct (ms <=? max_chunk) eqn:H1.
        { assert (H2 : (ms <=? max_safe) = true)
            by (apply Z.leb_le in H1; apply Z.leb_le; unfold max_chunk, max_safe in *; lia).
          rewrite H2. split; [|reflexivity].
          apply SF_intro with (set_code f (code f) (ResumeUnit k) AwaitingDurable);
            [stored Hfs | repeat split; simpl; assumption | own_awaited Hh]. }
        split; [|intros Hcf; discriminate (Hcf _ _ _ _ eq_refl)].
        apply SF_intro with (set_code f (code f) (ResumeUnit k) AwaitingDurable);
          [stored Hfs | repeat split; simpl; assumption | own_awaited Hh].
      * split; [|intros Hcf; discriminate (Hcf _ _ _ _ eq_refl)].
        apply SF_intro with (set_code f (code f) (ResumeUnit k) AwaitingDurable);
          [stored Hfs | repeat split; simpl; assumption | own_awaited Hh].
    + split; [|reflexivity]. apply SF_intro with (set_code f (k tt) NoPending Ready);
        [stored Hfs | apply fiber_ok_set; auto | none_awaited Ha].
    + match goal with
      | |- context [interrupt_fiber ?s target] =>
          destruct (interrupt_one s (set_code f (k tt) NoPending Ready) target)
            as (y & Hy & Hyok & Hya)
      end;
        [stored Hfs | apply fiber_ok_set; auto | exact Ha |].
      pose proof Hyok as (Hyh & _).
      rewrite Hy, Hh, find_one by exact Hyh.
      apply IH with y; [exact Hy | exact Hyh | exact Hyok | exact Hya].
    + split; [|reflexivity].
      apply SF_intro with (set_code f (code f) (ResumeNat k) WaitingOutside);
        [stored Hfs | repeat split; simpl; assumption | none_awaited Ha].
    + apply IH with g; [exact Hfs | exact Hg | apply fiber_ok_set; auto | exact Ha].
    + apply IH with g; [exact Hfs | exact Hg | apply fiber_ok_set; auto | exact Ha].
Qed.
