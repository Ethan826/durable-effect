(** * Lemmas about the executor, shared by the proofs of S1 and the statements derived from it.

    Three facts carry S1. First, the micro-step counter [micro] never changes what the
    executor does: every helper copies it, and only the arrival schedule reads it. Second, the
    arrival schedule is read in one place, at a turn boundary with an operation awaited, where
    it chooses between delivering and waiting; waiting changes nothing but [micro]. Third, a
    step only appends to the trace. *)

From Coq Require Import List ZArith Bool Arith.
From ITree Require Import Core.ITreeDefinition.
From Scheduling Require Import Model Executor Statements.
Import ListNotations.

(** ** The micro-step counter *)

(** The state with its micro-step counter replaced. *)
Definition set_micro (st : State) (m : nat) : State :=
  {| fibers := fibers st; queue := queue st; awaited := awaited st; abandoned := abandoned st;
     next_op := next_op st; next_sample := next_sample st; next_handle := next_handle st;
     draws := draws st; logical := logical st; memory := memory st; trace := trace st;
     micro := m; progress := progress st; finished := finished st |}.

Lemma set_micro_id : forall st, set_micro st (micro st) = st.
Proof. intros []; reflexivity. Qed.

Lemma trace_set_micro : forall st m, trace (set_micro st m) = trace st.
Proof. reflexivity. Qed.

Lemma finished_set_micro : forall st m, finished (set_micro st m) = finished st.
Proof. reflexivity. Qed.

Lemma set_micro_twice : forall st m j, set_micro (set_micro st m) j = set_micro st j.
Proof. reflexivity. Qed.

Lemma update_set_micro : forall st m fs q aw ab op sm hd dr l tr fd,
  update (set_micro st m) fs q aw ab op sm hd dr l tr fd
  = set_micro (update st fs q aw ab op sm hd dr l tr fd) m.
Proof. reflexivity. Qed.

Lemma with_fibers_set_micro : forall st m fs,
  with_fibers (set_micro st m) fs = set_micro (with_fibers st fs) m.
Proof. reflexivity. Qed.

Lemma tick_set_micro : forall st m b, tick (set_micro st m) b = set_micro (tick st b) (S m).
Proof. reflexivity. Qed.

(** A step that waits changes nothing but the counter. *)
Lemma tick_false : forall st, tick st false = set_micro st (S (micro st)).
Proof. reflexivity. Qed.

Lemma interrupt_fiber_set_micro : forall st m h,
  interrupt_fiber (set_micro st m) h = set_micro (interrupt_fiber st h) m.
Proof.
  intros st m h. unfold interrupt_fiber.
  change (fibers (set_micro st m)) with (fibers st).
  change (awaited (set_micro st m)) with (awaited st).
  destruct (find_fiber h (fibers st)) as [f|]; [|reflexivity].
  destruct (status f);
    try (destruct (awaited st) as [[h' op|h' op c r]|];
         try destruct (Nat.eqb h' h)); reflexivity.
Qed.

Lemma fold_interrupt_set_micro : forall fs st m,
  fold_left (fun s f => interrupt_fiber s (handle f)) fs (set_micro st m)
  = set_micro (fold_left (fun s f => interrupt_fiber s (handle f)) fs st) m.
Proof.
  induction fs as [|f fs IH]; intros st m; [reflexivity|].
  simpl. rewrite interrupt_fiber_set_micro. apply IH.
Qed.

Lemma end_attempt_set_micro : forall st m how,
  end_attempt (set_micro st m) how = set_micro (end_attempt st how) m.
Proof.
  intros st m []; [|reflexivity]. unfold end_attempt.
  change (fibers (set_micro st m)) with (fibers st).
  rewrite fold_interrupt_set_micro. reflexivity.
Qed.

Lemma resume_set_micro : forall st m h o,
  resume (set_micro st m) h o = set_micro (resume st h o) m.
Proof.
  intros st m h o. unfold resume.
  change (fibers (set_micro st m)) with (fibers st).
  destruct (find_fiber h (fibers st)); reflexivity.
Qed.

(** ** Environments with the same values *)

(** Closes [x = set_micro (run_fiber ... st' f') m] by the induction hypothesis, matching up to
    conversion: [simpl] leaves the recursive call in a form [rewrite] does not see. *)
Ltac apply_ih IH := refine (eq_trans _ (IH _ _ _ _)); reflexivity.

(** [run_fiber] reads the environment only through the random stream, and never reads the
    counter. *)
Lemma run_fiber_set_micro : forall pol P E1 E2,
  (forall n, random_of E1 n = random_of E2 n) ->
  forall fuel ops st f m,
    run_fiber pol P E1 fuel ops (set_micro st m) f
    = set_micro (run_fiber pol P E2 fuel ops st f) m.
Proof.
  intros pol P E1 E2 Hr. induction fuel as [|fuel IH]; intros ops st f m; [reflexivity|].
  cbn -[set_micro update emit with_fibers put_fiber set_code find_fiber new_fiber
        interrupt_fiber violate max_ops]. change (finished (set_micro st m)) with (finished st).
  destruct (finished st); [reflexivity|].
  destruct ops as [|ops]; [reflexivity|].
  destruct (observe (code f)) as [r|t|X e k]; [reflexivity|apply IH|].
  destruct e;
    cbn -[set_micro update emit with_fibers put_fiber set_code find_fiber new_fiber
          interrupt_fiber violate max_ops].
  - apply_ih IH.
  - rewrite Hr. apply_ih IH.
  - destruct f0.
    + apply_ih IH.
    + rewrite update_set_micro, IH.
      change (fibers (set_micro ?x m)) with (fibers x).
      destruct (find_fiber (handle f) (fibers (run_fiber pol P E2 fuel max_ops _ _)));
        [|reflexivity].
      apply_ih IH.
  - change (awaited (set_micro st m)) with (awaited st).
    destruct (awaited st); reflexivity.
  - change (awaited (set_micro st m)) with (awaited st).
    destruct (chunk_long_sleeps pol), d as [ms|];
      try destruct (ms <=? 0)%Z; try destruct (ms <=? max_chunk)%Z;
      try destruct (ms <=? max_safe)%Z; try destruct (awaited st); reflexivity.
  - reflexivity.
  - rewrite with_fibers_set_micro, interrupt_fiber_set_micro.
    change (fibers (set_micro ?x m)) with (fibers x).
    destruct (find_fiber (handle f) (fibers (interrupt_fiber _ n))); [|reflexivity].
    apply_ih IH.
  - reflexivity.
  - apply_ih IH.
  - apply_ih IH.
Qed.

Lemma cancel_set_micro : forall st m op h,
  cancel (set_micro st m) op h = set_micro (cancel st op h) m.
Proof. intros st m op h. unfold cancel. rewrite <- interrupt_fiber_set_micro. reflexivity. Qed.

Lemma deliver_set_micro : forall E1 E2 st m aw,
  same_values E1 E2 ->
  deliver E1 (set_micro st m) aw = set_micro (deliver E2 st aw) m.
Proof.
  intros E1 E2 st m aw (Ho & Hs & Hc & Hr). unfold deliver, take_sample.
  destruct aw as [h op|h op chunk rest]; rewrite Hc;
    destruct (cancelled_at E2 op); rewrite ?Ho, !Hs.
  - rewrite <- cancel_set_micro. reflexivity.
  - rewrite <- resume_set_micro. reflexivity.
  - rewrite <- cancel_set_micro. reflexivity.
  - destruct rest as [|d|]; [rewrite <- resume_set_micro| |]; try reflexivity.
    destruct (d <=? max_chunk)%Z; reflexivity.
Qed.

Lemma finish_set_micro : forall st m e, finish (set_micro st m) e = set_micro (finish st e) m.
Proof. reflexivity. Qed.

Lemma violate_set_micro : forall st m v,
  violate (set_micro st m) v = set_micro (violate st v) m.
Proof. reflexivity. Qed.

(** ** One step *)

(** The schedule under which every result has arrived from the start: a replay. *)
Definition arrived : Arrival := fun _ _ => true.

(** The ending the environment chooses at this state, if any. *)
Definition fires (E : Env) (st : State) : option Ending :=
  match ends_at E with
  | Some (n, how) => if Nat.eqb n (progress st) then Some how else None
  | None => None
  end.

Lemma run_head_set_micro : forall pol P E1 E2 st m h rest,
  (forall n, random_of E1 n = random_of E2 n) ->
  run_head pol P E1 (set_micro st m) h rest = set_micro (run_head pol P E2 st h rest) (S m).
Proof.
  intros pol P E1 E2 st m h rest Hr. unfold run_head. cbn zeta.
  match goal with
  | |- match find_fiber h (fibers ?A) with _ => _ end
       = set_micro (match find_fiber h (fibers ?B) with _ => _ end) _ =>
      change A with (set_micro B m); change (fibers (set_micro B m)) with (fibers B);
      destruct (find_fiber h (fibers B)) as [f|]
  end; [destruct (status f)|];
    rewrite ?(run_fiber_set_micro _ _ _ _ Hr), tick_set_micro; reflexivity.
Qed.

(** The step of an unfinished state that does not end the attempt. Shared by the two branches
    of [step] on [ends_at]. *)
Ltac turn_set_micro Hv Hr :=
  change (queue (set_micro ?x ?j)) with (queue x);
  match goal with |- context [queue ?x] => destruct (queue x) end;
  [ change (awaited (set_micro ?x ?j)) with (awaited x);
    match goal with |- context [awaited ?x] => destruct (awaited x) end;
    [ cbn -[set_micro deliver tick];
      rewrite (deliver_set_micro _ _ _ _ _ Hv), tick_set_micro; reflexivity
    | change (root_done (set_micro ?x ?j)) with (root_done x);
      match goal with |- context [root_done ?x] => destruct (root_done x) end;
      [ rewrite finish_set_micro, tick_set_micro; reflexivity
      | match goal with |- context [blocked_is_violation ?p] =>
          destruct (blocked_is_violation p) end;
        [rewrite violate_set_micro, tick_set_micro | rewrite tick_set_micro];
        reflexivity ] ]
  | apply (run_head_set_micro _ _ _ _ _ _ _ _ Hr) ].

(** In a replay, a step commutes with the counter, and environments with the same values and
    the same ending at this state take the same step. *)
Lemma step_set_micro : forall pol P E1 E2 st m,
  same_values E1 E2 -> fires E1 st = fires E2 st -> finished st = None ->
  step pol P E1 arrived no_outside_resumes (set_micro st m)
  = set_micro (step pol P E2 arrived no_outside_resumes st) (S m).
Proof.
  intros pol P E1 E2 st m Hv Hf Hn. pose proof Hv as (_ & _ & _ & Hr).
  unfold step. change (finished (set_micro st m)) with (finished st). rewrite Hn.
  change (no_outside_resumes _) with (@None (nat * nat)). cbv iota.
  change (progress (set_micro st m)) with (progress st).
  unfold fires in Hf.
  destruct (ends_at E1) as [[n1 h1]|], (ends_at E2) as [[n2 h2]|];
    try destruct (Nat.eqb n1 (progress st)); try destruct (Nat.eqb n2 (progress st));
    try discriminate Hf;
    try (injection Hf as <-; rewrite end_attempt_set_micro, tick_set_micro; reflexivity);
    turn_set_micro Hv Hr.
Qed.

(** The arrival schedule only chooses between the replay's step and waiting. *)
Lemma step_cases : forall pol P E A st,
  step pol P E A no_outside_resumes st = step pol P E arrived no_outside_resumes st \/
  step pol P E A no_outside_resumes st = tick st false.
Proof.
  intros pol P E A st. unfold step.
  destruct (finished st); [left; reflexivity|].
  change (no_outside_resumes _) with (@None (nat * nat)). cbv iota.
  destruct (ends_at E) as [[n how]|];
    [destruct (Nat.eqb n (progress st)); [left; reflexivity|]|];
    (destruct (queue st); [|left; reflexivity]);
    (destruct (awaited st) as [aw|]; [|left; reflexivity]);
    (destruct (A (awaited_op aw) (micro st)); [left|right]; reflexivity).
Qed.

Lemma step_finished : forall pol P E A X st e,
  finished st = Some e -> step pol P E A X st = st.
Proof. intros pol P E A X st e H. unfold step. rewrite H. reflexivity. Qed.

Lemma iterate_S : forall pol P E A X n st,
  iterate pol P E A X (S n) st = step pol P E A X (iterate pol P E A X n st).
Proof.
  intros pol P E A X n. induction n as [|n IH]; intros st; [reflexivity|].
  change (iterate pol P E A X (S (S n)) st)
    with (iterate pol P E A X (S n) (step pol P E A X st)).
  rewrite IH. reflexivity.
Qed.

Lemma initial_same : forall P E1 E2,
  (forall n, sample_of E1 n = sample_of E2 n) -> initial P E1 = initial P E2.
Proof. intros P E1 E2 Hs. unfold initial. rewrite Hs. reflexivity. Qed.

(** ** The trace only grows *)

Lemma prefix_refl : forall {X} (l : list X), prefix l l.
Proof. intros X l. exists []. symmetry. apply app_nil_r. Qed.

Lemma prefix_trans : forall {X} (l1 l2 l3 : list X),
  prefix l1 l2 -> prefix l2 l3 -> prefix l1 l3.
Proof.
  intros X l1 l2 l3 [r1 ->] [r2 ->]. exists (r1 ++ r2). symmetry. apply app_assoc.
Qed.

Lemma prefix_app : forall {X} (l r : list X), prefix l (l ++ r).
Proof. intros X l r. exists r. reflexivity. Qed.

(** Closes [prefix (trace st) (trace s)] where [s] is built from [st] by record updates that
    append to the trace. It matches the goal's shape before applying anything: unifying a
    trace with the trace of [run_fiber] would unfold [max_ops] steps of it. *)
Ltac solve_prefix :=
  cbn [trace emit update with_fibers finish violate set_code tick take_sample];
  repeat rewrite <- app_assoc;
  match goal with
  | |- prefix _ (_ ++ _) => apply prefix_app
  | |- prefix _ _ => apply prefix_refl
  end.

Lemma interrupt_fiber_prefix : forall st h,
  prefix (trace st) (trace (interrupt_fiber st h)).
Proof.
  intros st h. unfold interrupt_fiber.
  destruct (find_fiber h (fibers st)) as [f|]; [|apply prefix_refl].
  destruct (status f);
    try (destruct (awaited st) as [[h' op|h' op c r]|];
         try destruct (Nat.eqb h' h)); solve_prefix.
Qed.

Lemma fold_interrupt_prefix : forall fs st,
  prefix (trace st) (trace (fold_left (fun s f => interrupt_fiber s (handle f)) fs st)).
Proof.
  induction fs as [|f fs IH]; intros st; [apply prefix_refl|].
  simpl. eapply prefix_trans; [apply interrupt_fiber_prefix|apply IH].
Qed.

Lemma end_attempt_prefix : forall st how, prefix (trace st) (trace (end_attempt st how)).
Proof.
  intros st []; unfold end_attempt; [|solve_prefix].
  eapply prefix_trans; [apply fold_interrupt_prefix|solve_prefix].
Qed.

Lemma resume_prefix : forall st h o, prefix (trace st) (trace (resume st h o)).
Proof.
  intros st h o. unfold resume. destruct (find_fiber h (fibers st)); solve_prefix.
Qed.

(** Chains [prefix (trace st) (trace (F s'))] through [prefix (trace st) (trace s')]. *)
Ltac chain_prefix lemma := eapply prefix_trans; [|apply lemma]; solve_prefix.

Lemma run_fiber_prefix : forall pol P E fuel ops st f,
  prefix (trace st) (trace (run_fiber pol P E fuel ops st f)).
Proof.
  intros pol P E. induction fuel as [|fuel IH]; intros ops st f; [solve_prefix|].
  cbn -[update emit with_fibers put_fiber set_code find_fiber new_fiber
        interrupt_fiber violate max_ops].
  destruct (finished st); [apply prefix_refl|].
  destruct ops as [|ops]; [solve_prefix|].
  destruct (observe (code f)) as [r|t|X e k]; [solve_prefix|apply IH|].
  destruct e;
    cbn -[update emit with_fibers put_fiber set_code find_fiber new_fiber
          interrupt_fiber violate max_ops].
  - chain_prefix IH.
  - chain_prefix IH.
  - destruct f0.
    + chain_prefix IH.
    + match goal with |- context [run_fiber pol P E fuel max_ops ?A ?c] =>
        assert (Hc := IH max_ops A c) end.
      match goal with |- context [find_fiber ?hd (fibers ?B)] =>
        destruct (find_fiber hd (fibers B)) end.
      * eapply prefix_trans; [|apply IH]. eapply prefix_trans; [|apply Hc]. solve_prefix.
      * eapply prefix_trans; [|apply Hc]. solve_prefix.
  - destruct (awaited st); solve_prefix.
  - destruct (chunk_long_sleeps pol), d as [ms|];
      try destruct (ms <=? 0)%Z; try destruct (ms <=? max_chunk)%Z;
      try destruct (ms <=? max_safe)%Z; try destruct (awaited st); solve_prefix.
  - solve_prefix.
  - match goal with |- context [interrupt_fiber ?A n] =>
      assert (Hi := interrupt_fiber_prefix A n) end.
    match goal with |- context [find_fiber ?hd (fibers ?B)] =>
      destruct (find_fiber hd (fibers B)) end.
    + eapply prefix_trans; [|apply IH]. eapply prefix_trans; [|apply Hi]. solve_prefix.
    + eapply prefix_trans; [|apply Hi]. solve_prefix.
  - solve_prefix.
  - chain_prefix IH.
  - chain_prefix IH.
Qed.

Lemma deliver_prefix : forall E st aw, prefix (trace st) (trace (deliver E st aw)).
Proof.
  intros E st aw. unfold deliver.
  destruct aw as [h op|h op chunk rest]; destruct (cancelled_at E op).
  - chain_prefix interrupt_fiber_prefix.
  - chain_prefix resume_prefix.
  - chain_prefix interrupt_fiber_prefix.
  - destruct rest as [|d|]; [chain_prefix resume_prefix| |solve_prefix].
    destruct (d <=? max_chunk)%Z; solve_prefix.
Qed.

Lemma trace_tick : forall st b, trace (tick st b) = trace st.
Proof. reflexivity. Qed.

(** The fiber's run is named before the trace is compared: the kernel would otherwise check
    [trace (tick r true)] against [trace r] by unfolding [max_ops] steps of [r]. *)
Lemma run_head_prefix : forall pol P E st h rest,
  prefix (trace st) (trace (run_head pol P E st h rest)).
Proof.
  intros pol P E st h rest. unfold run_head. cbn zeta.
  match goal with |- context [find_fiber h (fibers ?B)] =>
    destruct (find_fiber h (fibers B)) as [f|] end; [destruct (status f)|];
    rewrite trace_tick; try solve_prefix.
  match goal with |- context [run_fiber ?a ?b ?c ?d ?e ?s ?g] =>
    pose proof (run_fiber_prefix a b c d e s g) as Hp;
    remember (run_fiber a b c d e s g) as r eqn:Er; clear Er end.
  eapply prefix_trans; [|exact Hp]. solve_prefix.
Qed.

Lemma step_prefix : forall pol P E A X st,
  prefix (trace st) (trace (step pol P E A X st)).
Proof.
  intros pol P E A X st. unfold step.
  destruct (finished st); [apply prefix_refl|].
  destruct (X (micro st)) as [[h v]|].
  { destruct (find_fiber h (fibers st)) as [f|]; [destruct (status f)|]; solve_prefix. }
  destruct (ends_at E) as [[n how]|];
    [destruct (Nat.eqb n (progress st)); [chain_prefix end_attempt_prefix|]|];
    (destruct (queue st) as [|h rest];
     [ destruct (awaited st) as [aw|];
       [ destruct (A (awaited_op aw) (micro st)); [chain_prefix deliver_prefix|solve_prefix]
       | destruct (root_done st); [|destruct (blocked_is_violation pol)]; solve_prefix ]
     | apply run_head_prefix ]).
Qed.

Lemma iterate_prefix : forall pol P E A X n m st, (n <= m)%nat ->
  prefix (trace (iterate pol P E A X n st)) (trace (iterate pol P E A X m st)).
Proof.
  intros pol P E A X n m st Hle. induction Hle as [|m Hle IH]; [apply prefix_refl|].
  rewrite iterate_S. eapply prefix_trans; [apply IH|apply step_prefix].
Qed.
