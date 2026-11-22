(** * Definitions and list lemmas for the proofs of S8 (the time domain).

    The claims P2 to P9 are properties of the trace. Each is proved as an invariant of the
    executor's state as the trace grows. This file holds the pieces every such invariant
    uses: the suffix of a trace after the last action of a kind, claims about every action
    of a trace given what came before it, and the predicates the invariants are made of. *)

From Coq Require Import List ZArith Bool Arith Lia Sorting.
From Durable Require Import Runtime Exec Rev3 Statements.
Import ListNotations.
Open Scope Z_scope.

(** ** The suffix after the last action of a kind *)

(** The last action of [t] that satisfies [p], and the actions after it. *)
Fixpoint time_after_last (p : Action -> bool) (t : list Action)
    : option (Action * list Action) :=
  match t with
  | [] => None
  | a :: r =>
      match time_after_last p r with
      | Some res => Some res
      | None => if p a then Some (a, r) else None
      end
  end.

Lemma time_after_last_snoc : forall p t a,
  time_after_last p (t ++ [a]) =
  if p a then Some (a, [])
  else match time_after_last p t with
       | Some (b, s) => Some (b, s ++ [a])
       | None => None
       end.
Proof.
  intros p t a. induction t as [|b t IH]; simpl.
  - destruct (p a); reflexivity.
  - rewrite IH. destruct (p a) eqn:Ha; [reflexivity|].
    destruct (time_after_last p t) as [[c s]|]; [reflexivity|].
    destruct (p b); reflexivity.
Qed.

Lemma time_after_last_none : forall p t,
  existsb p t = false -> time_after_last p t = None.
Proof.
  intros p t. induction t as [|a t IH]; simpl; [reflexivity|].
  intros H. apply orb_false_iff in H as [H1 H2]. rewrite IH by exact H2. rewrite H1.
  reflexivity.
Qed.

Lemma time_after_last_none_iff : forall p t,
  time_after_last p t = None -> existsb p t = false.
Proof.
  intros p t. induction t as [|a t IH]; simpl; [reflexivity|].
  destruct (time_after_last p t); [discriminate|].
  destruct (p a) eqn:Ha; [discriminate|]. intros _. rewrite IH; reflexivity.
Qed.

Lemma time_after_last_app : forall p pre b post,
  p b = true -> existsb p post = false ->
  time_after_last p (pre ++ b :: post) = Some (b, post).
Proof.
  intros p pre b post Hb Hpost. induction pre as [|c pre IH]; simpl.
  - rewrite time_after_last_none by exact Hpost. rewrite Hb. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma time_after_last_some : forall p t b s,
  time_after_last p t = Some (b, s) ->
  p b = true /\ existsb p s = false /\ exists pre, t = pre ++ b :: s.
Proof.
  intros p t. induction t as [|a t IH]; simpl; intros b s H; [discriminate|].
  destruct (time_after_last p t) as [[b' s']|] eqn:Ht.
  - inversion H; subst. destruct (IH b s eq_refl) as [H1 [H2 [pre Hpre]]].
    split; [exact H1|]. split; [exact H2|]. exists (a :: pre). rewrite Hpre. reflexivity.
  - destruct (p a) eqn:Ha; [|discriminate]. inversion H; subst.
    split; [exact Ha|]. split; [apply time_after_last_none_iff; exact Ht|].
    exists []. reflexivity.
Qed.

Lemma time_existsb_after_last : forall p t,
  existsb p t = true -> exists b s, time_after_last p t = Some (b, s).
Proof.
  intros p t H. destruct (time_after_last p t) as [[b s]|] eqn:E; [eauto|].
  apply time_after_last_none_iff in E. congruence.
Qed.

(** ** Claims about every action of a trace *)

(** [C pre a] holds for every action [a] of [t], with [pre] the actions before it. *)
Definition time_claims (C : list Action -> Action -> Prop) (t : list Action) : Prop :=
  forall pre a post, t = pre ++ a :: post -> C pre a.

Lemma time_claims_nil : forall C, time_claims C [].
Proof. intros C pre a post H. destruct pre; discriminate. Qed.

Lemma time_claims_snoc : forall C t a,
  time_claims C t -> C t a -> time_claims C (t ++ [a]).
Proof.
  intros C t a Ht Ha pre b post H.
  destruct (exists_last (l := b :: post) ltac:(discriminate)) as [init [z Hz]].
  destruct post as [|p post].
  - simpl in Hz. replace (pre ++ [b]) with (pre ++ [b]) in H by reflexivity.
    apply app_inj_tail in H as [-> ->]. exact Ha.
  - destruct (exists_last (l := p :: post) ltac:(discriminate)) as [mid [w Hw]].
    rewrite Hw in H. rewrite app_comm_cons, app_assoc in H.
    apply app_inj_tail in H as [H _]. apply (Ht pre b mid). rewrite H. reflexivity.
Qed.

(** ** Kinds of action *)

Definition time_is_start (f : FiberId) (tok : Token) (a : Action) : bool :=
  match a with AStart f' tok' _ => Nat.eqb f f' && Nat.eqb tok tok' | _ => false end.

Definition time_is_owned (f : FiberId) (tok : Token) (a : Action) : bool :=
  match a with
  | ACommand _ _ (Some (f', tok')) => Nat.eqb f f' && Nat.eqb tok tok'
  | _ => false
  end.

Definition time_is_cmd (a : Action) : bool :=
  match a with ACommand _ _ _ => true | _ => false end.

Definition time_is_sample (a : Action) : bool :=
  match a with ASampled _ _ _ _ => true | _ => false end.

(** A sample that credits no chunk. *)
Definition time_is_plain (a : Action) : bool :=
  match a with ASampled _ _ _ None => true | _ => false end.

(** The tokens of the operations a trace reports started. *)
Definition time_stoks (t : list Action) : list Token :=
  flat_map (fun a => match a with AStart _ tok _ => [tok] | _ => [] end) t.

(** The fact taken from I4: no token is started twice in a trace. *)
Definition time_fresh_tokens : Prop :=
  forall R, Meets R -> forall p I Sch n, NoDup (time_stoks (run R p I Sch n)).

(** ** Sums and chains *)

Definition time_sum (l : list Z) : Z := fold_right Z.add 0 l.

Definition time_bounds (l : list Z) : Prop := Forall (fun k => 1 <= k <= max_chunk) l.

Definition time_rem (c : Chain) : Z := match c with Remaining r => r | _ => 0 end.

(** What remains of a sleep [op] after the credits [cr] and the current link [k] and [rest]:
    a finite sleep's chain sums to its duration, and an infinite one never ends. *)
Definition time_chain_ok (op : Op) (cr : list Z) (k : Z) (rest : Chain) : Prop :=
  match op with
  | OSleep (Millis d) =>
      (rest = NoChain \/ exists r, rest = Remaining r /\ 1 <= r) /\
      time_sum cr + k + time_rem rest = d
  | OSleep Forever => rest = Endless
  | ORun _ _ => False
  end.

Definition time_total_ok (op : Op) (cr : list Z) : Prop :=
  match op with OSleep (Millis d) => time_sum cr = d | _ => False end.

(** A sleep that issues a chain: a positive duration or forever. *)
Definition time_sleepy (op : Op) : Prop :=
  match op with OSleep (Millis d) => 0 < d | OSleep Forever => True | ORun _ _ => False end.

(** ** Subscriptions and waiters *)

(** The subscription leads to a delivery for fiber [f]'s await of [tok]. *)
Definition time_sub_live (f : FiberId) (tok : Token) (s : option Sub) : bool :=
  match s with
  | Some (SOp _ f' tok' _ _ _) | Some (SSample _ (FResult f' tok' _))
  | Some (SSample _ (FLink f' tok' _ _)) => Nat.eqb f f' && Nat.eqb tok tok'
  | _ => false
  end.

(** The subscription belongs to fiber [f]'s await of [tok]. *)
Definition time_sub_refs (f : FiberId) (tok : Token) (s : option Sub) : bool :=
  match s with
  | Some (SOp _ f' tok' _ _ _) | Some (SSample _ (FResult f' tok' _))
  | Some (SSample _ (FLink f' tok' _ _)) | Some (SSample _ (FCancelled f' tok')) =>
      Nat.eqb f f' && Nat.eqb tok tok'
  | _ => false
  end.

(** A subscription that no fiber awaits and that applies no sample. *)
Definition time_idle (s : option Sub) : bool :=
  match s with
  | None | Some (SReleased _) | Some (SSample _ (FReleased _ _ _)) => true
  | _ => false
  end.

Definition time_waiter_is (f : FiberId) (tok : Token) (w : option (FiberId * Token * Op))
    : bool :=
  match w with Some (f', tok', _) => Nat.eqb f f' && Nat.eqb tok tok' | None => false end.

Definition time_nodel (f : FiberId) (tok : Token) (q : list Task) : Prop :=
  forall o, ~ In (Deliver f tok o) q.

(** ** Small facts *)

Lemma time_eqb_pair : forall f f' tok tok',
  (Nat.eqb f f' && Nat.eqb tok tok') = true <-> f = f' /\ tok = tok'.
Proof.
  intros. rewrite andb_true_iff, !Nat.eqb_eq. tauto.
Qed.

Lemma time_stoks_app : forall a b, time_stoks (a ++ b) = time_stoks a ++ time_stoks b.
Proof. intros. unfold time_stoks. apply flat_map_app. Qed.

Lemma time_nodup_prefix : forall a b, NoDup (time_stoks (a ++ b)) -> NoDup (time_stoks a).
Proof.
  intros a b H. rewrite time_stoks_app in H. apply NoDup_app_remove_r in H. exact H.
Qed.

Lemma time_in_stoks : forall f tok t,
  existsb (time_is_start f tok) t = true -> In tok (time_stoks t).
Proof.
  intros f tok t H. apply existsb_exists in H as [a [Ha Hs]].
  destruct a; try discriminate. simpl in Hs. apply time_eqb_pair in Hs as [-> ->].
  unfold time_stoks. apply in_flat_map. exists (AStart f0 tok0 op). simpl. auto.
Qed.

(** A token started now was not started before. *)
Lemma time_fresh : forall t f tok op g,
  NoDup (time_stoks (t ++ [AStart f tok op])) -> existsb (time_is_start g tok) t = false.
Proof.
  intros t f tok op g H. destruct (existsb (time_is_start g tok) t) eqn:E; [|reflexivity].
  exfalso. apply time_in_stoks in E. rewrite time_stoks_app in H. simpl in H.
  apply NoDup_remove_2 in H. rewrite app_nil_r in H. apply H. exact E.
Qed.

Lemma time_credits_app : forall f tok a b,
  credits f tok (a ++ b) = credits f tok a ++ credits f tok b.
Proof. intros. unfold credits. apply flat_map_app. Qed.

Lemma time_applied_app : forall a b, applied (a ++ b) = applied a ++ applied b.
Proof. intros. unfold applied. apply flat_map_app. Qed.

Lemma time_lvalues_app : forall a b, lvalues (a ++ b) = lvalues a ++ lvalues b.
Proof. intros. unfold lvalues. apply flat_map_app. Qed.

Lemma time_sum_app : forall a b, time_sum (a ++ b) = time_sum a + time_sum b.
Proof.
  intros a b. induction a as [|x a IH]; simpl; [reflexivity|]. rewrite IH. lia.
Qed.
