(** * Statements S1 to S11 of #37, revision 9, with S8's claims P1 to P9.

    Each statement is a named proposition, with no proof. The statements that depend on the
    runtime take [Meets R] as a hypothesis; the dossier's table says which interface
    properties each one uses. The owner's interface (proof-dossier, section 7). *)

From Coq Require Import List ZArith Bool Arith Sorting.
From Durable Require Import Runtime Exec Rev3.
Import ListNotations.
Open Scope Z_scope.

(** ** Comparing traces *)

Definition prefix {X} (a b : list X) : Prop := exists r, b = a ++ r.
Definition compatible {X} (a b : list X) : Prop := prefix a b \/ prefix b a.

(** A trace up to its cut, with the cut and everything after it left out (X3). *)
Fixpoint before_cut (t : list Action) : list Action :=
  match t with
  | [] => []
  | ACut _ :: _ => []
  | a :: rest => a :: before_cut rest
  end.

(** An arrival schedule: entries arrive in order and never leave, and at most all of them. *)
Definition valid_schedule (I : Inputs) (Sch : Schedule) : Prop :=
  (forall i j, (i <= j)%nat -> (arrived Sch i <= arrived Sch j)%nat) /\
  (forall i, (arrived Sch i <= length (entries I))%nat).

(** An attempt started from runtime state [r] in place of [init R p (seed I)]: I1 is about
    equivalent states, so the statements that use it start from any state equivalent to the
    initial one. *)
Definition start_from (R : Runtime) (p : prog R) (I : Inputs) (r : rstate R) : Sys R :=
  {| xs := xs (initial R p I); rs := r |}.

Definition run_from (R : Runtime) (p : prog R) (I : Inputs) (Sch : Schedule) (r : rstate R)
    (n : nat) : list Action :=
  trace (xs (iterate R I Sch n (start_from R p I r))).

Definition reachable (R : Runtime) (p : prog R) (I : Inputs) (Sch : Schedule) (s : Sys R)
    : Prop :=
  exists n, s = iterate R I Sch n (initial R p I).

(** No stop, foreign input or cut is due, so the step is the executor's own. *)
Definition quiet (I : Inputs) (Sch : Schedule) (x : XState) : Prop :=
  stop_due Sch x = false /\ foreign_due I x = None /\ cut_due Sch x = None.

(** ** S1. Arrival independence *)

(** Two attempts with the same inputs, from equivalent runtime states, give traces that agree
    up to their common cut, whatever the arrival schedules, cuts and step counts. *)
Definition S1 : Prop :=
  forall R, Meets R -> forall p I Sch1 Sch2 r1 r2 n1 n2,
    valid_schedule I Sch1 -> valid_schedule I Sch2 ->
    requiv R r1 (init R p (seed I)) -> requiv R r2 (init R p (seed I)) ->
    compatible (before_cut (run_from R p I Sch1 r1 n1)) (before_cut (run_from R p I Sch2 r2 n2)).

(** ** S2. Replay *)

Definition commands (t : list Action) : list CmdKind :=
  flat_map (fun a => match a with ACommand _ k _ => [k] | _ => [] end) t.

(** A replay of an attempt: the replay's persisted journal is the commands the attempt issued
    before its cut, it consumes the entries the attempt consumed and possibly more after
    them, and its foreign inputs agree up to the attempt's last task. The replay starts from
    any runtime state equivalent to the initial one, as it may run in another process. Then
    the replay never fails with a journal mismatch, and the two traces agree up to their
    common cut. *)
Definition S2 : Prop :=
  forall R, Meets R -> forall p I Sch n I' Sch' n' more r',
    requiv R r' (init R p (seed I')) ->
    valid_schedule I Sch -> valid_schedule I' Sch' ->
    let x := xs (iterate R I Sch n (initial R p I)) in
    ~ In (AExit VMismatch) (trace x) ->
    persisted I' = commands (before_cut (trace x)) ->
    entries I' = firstn (cursor x) (entries I) ++ more ->
    (forall k, (k <= progress x)%nat -> foreign I' k = foreign I k) ->
    stream I' = stream I -> seed I' = seed I ->
    let t' := run_from R p I' Sch' r' n' in
    ~ In (AExit VMismatch) t' /\ compatible (before_cut (trace x)) (before_cut t').

(** P1, that replay gives the same [L] at every point the replayed prefix determines, follows
    from S2: [L] after each sample is recorded in the trace. *)

(** ** S3. Violations at the same position *)

Definition S3 : Prop :=
  forall R, Meets R -> forall p I Sch1 Sch2 n1 n2 i v,
    valid_schedule I Sch1 -> valid_schedule I Sch2 ->
    let t1 := before_cut (run R p I Sch1 n1) in
    let t2 := before_cut (run R p I Sch2 n2) in
    nth_error t1 i = Some (AViolation v) -> (i < length t2)%nat ->
    nth_error t2 i = Some (AViolation v).

(** ** S4. One awaiter *)

(** While the attempt is open, the fiber waiting for the slot and the fiber whose operation
    is subscribed are the one awaiter; and a fiber starting a durable operation while any
    fiber awaits, itself included, is a violation, with no command issued. A run step's action
    runs only after its command, so it does not run. *)
Definition S4 : Prop :=
  (forall R, Meets R -> forall p I Sch s, reachable R p I Sch s -> phase (xs s) = POpen ->
     (forall f tok op, waiter (xs s) = Some (f, tok, op) -> awaiter (xs s) = Some (f, tok)) /\
     (forall c f tok op k rest, sub (xs s) = Some (SOp c f tok op k rest) ->
        awaiter (xs s) = Some (f, tok))) /\
  (forall I x f tok op, phase x = POpen -> violated x = false -> awaiter x <> None ->
     zero_sleep op = false ->
     trace (on_start I x f tok op) = trace x ++ [AStart f tok op; AViolation SecondOp] /\
     phase (on_start I x f tok op) <> POpen).

(** ** S5. Foreign resumes and interruptions *)

(** A foreign resume or interruption, while no violation has been recorded, is recorded as a
    violation and nothing else, the runtime is not called, and the attempt closes. After an
    earlier violation it changes nothing: only the first is recorded (X6). *)
Definition S5 : Prop :=
  forall R p I Sch s g, reachable R p I Sch s -> phase (xs s) <> PDone ->
    violated (xs s) = false -> stop_due Sch (xs s) = false ->
    (foreign_due I (xs s) = Some (FResume g) \/ foreign_due I (xs s) = Some (FInterrupt g)) ->
    let s' := step R I Sch s in
    rs s' = rs s /\
    (exists v, trace (xs s') = trace (xs s) ++ [AViolation v]) /\ phase (xs s') <> POpen.

(** After any violation, every exit is [VDefect]. *)
Definition S5_exit : Prop :=
  forall R, Meets R -> forall p I Sch n v w,
    In (AViolation v) (run R p I Sch n) -> In (AExit w) (run R p I Sch n) -> w = VDefect.

(** ** S6. The next transition at a turn boundary *)

Definition S6 : Prop :=
  forall R p I Sch s, reachable R p I Sch s -> quiet I Sch (xs s) -> queue (xs s) = [] ->
    let x := xs s in
    let x' := xs (step R I Sch s) in
    (** blocked: the violation is recorded *)
    (phase x = POpen -> sub x = None -> waiter x = None ->
       trace x' = trace x ++ [AViolation Blocked]) /\
    (** something is subscribed and nothing has arrived: the executor waits *)
    (phase x = POpen -> forall sb, sub x = Some sb ->
       ~ (held x = true /\ waiter x <> None) -> (arrived Sch (micro x) <= cursor x)%nat ->
       trace x' = trace x /\ queue x' = [] /\ sub x' = sub x) /\
    (** the slot is free and a fiber waits: a local turn issues its command *)
    (phase x = POpen -> held x = false -> sub x = None -> forall f tok op,
       waiter x = Some (f, tok, op) ->
       (exists c k, trace x' = trace x ++ [ACommand c k (Some (f, tok))]) \/
       In (AExit VMismatch) (trace x')) /\
    (** a cancellation is held and a fiber waits: it is delivered *)
    (phase x = POpen -> held x = true -> forall f tok op,
       waiter x = Some (f, tok, op) -> queue x' = [DeliverCancel f tok]) /\
    (** during closing, an empty queue ends closing *)
    (forall c, phase x = PClosing c -> phase x' = PDone).

(** ** S7. One cause per turn *)

(** A turn boundary consumes at most one journal entry; a local turn consumes none; and when
    the earliest arrived entry concerns the subscription, the next step consumes it. *)
Definition S7 : Prop :=
  forall R p I Sch s, reachable R p I Sch s -> quiet I Sch (xs s) -> queue (xs s) = [] ->
    phase (xs s) = POpen ->
    let x := xs s in
    let x' := xs (step R I Sch s) in
    (cursor x' <= S (cursor x))%nat /\
    ((held x = true /\ waiter x <> None) \/ sub x = None -> cursor x' = cursor x) /\
    (forall sb, sub x = Some sb -> ~ (held x = true /\ waiter x <> None) ->
       (cursor x < arrived Sch (micro x))%nat ->
       (nth_error (entries I) (cursor x) = Some InCancel \/
        exists r, nth_error (entries I) (cursor x) = Some (InNotify (sub_cmd sb) r)) ->
       cursor x' = S (cursor x)).

(** ** S8. The time rule *)

(** The values of [L] the trace records: after each applied sample, and at each clock read. *)
Definition lvalues (t : list Action) : list Z :=
  flat_map (fun a => match a with ASampled _ _ l _ | AClock _ l => [l] | _ => [] end) t.

(** P2: [L] never decreases. *)
Definition P2 : Prop :=
  forall R, Meets R -> forall p I Sch n, Sorted Z.le (lvalues (run R p I Sch n)).

(** The chunks credited to fiber [f]'s await of [tok]. *)
Definition credits (f : FiberId) (tok : Token) (t : list Action) : list Z :=
  flat_map (fun a => match a with
                     | ASampled _ _ _ (Some (f', tok', k)) =>
                         if Nat.eqb f f' && Nat.eqb tok tok' then [k] else []
                     | _ => [] end) t.

Definition starts (f : FiberId) (tok : Token) (t : list Action) : Prop :=
  exists op, In (AStart f tok op) t.

(** P3 and P9: the chunks credited for a delivered sleep of [d > 0] sum to [d], and each is
    between 1 and 2^31 - 1 ms. *)
Definition P3 : Prop :=
  forall R, Meets R -> forall p I Sch n pre mid post f tok d o,
    run R p I Sch n = pre ++ AStart f tok (OSleep (Millis d)) :: mid ++
                      ADelivered f tok o :: post ->
    ~ starts f tok mid -> 0 < d ->
    fold_right Z.add 0 (credits f tok mid) = d /\
    Forall (fun k => 1 <= k <= max_chunk) (credits f tok mid).

(** P9, the infinite sleep: it is never delivered. *)
Definition P9 : Prop :=
  forall R, Meets R -> forall p I Sch n pre mid post f tok o,
    run R p I Sch n = pre ++ AStart f tok (OSleep Forever) :: mid ++
                      ADelivered f tok o :: post ->
    starts f tok mid.

(** The applied samples, in order: reading, [L] after it, and the chunk it credits. *)
Definition applied (t : list Action) : list (Z * Z * Z) :=
  flat_map (fun a => match a with
                     | ASampled _ s l cr =>
                         [(s, l, match cr with Some (_, _, k) => k | None => 0 end)]
                     | _ => [] end) t.

Definition reading (e : Z * Z * Z) : Z := fst (fst e).
Definition lafter (e : Z * Z * Z) : Z := snd (fst e).
Definition chunk (e : Z * Z * Z) : Z := snd e.

(** P4: [L] is at least every applied sample; with P2, at least every earlier one. *)
Definition P4 : Prop :=
  forall R, Meets R -> forall p I Sch n e,
    In e (applied (run R p I Sch n)) -> reading e <= lafter e.

(** P5 (S8'). Give each applied sample a true time; suppose each reading is at most its true
    time plus [E], true time does not decrease, and a sample that credits a chunk [k] has a
    true time at least [k - lead] after the previous sample's: the early-fire hypothesis,
    for credited chunks only. Then [L] after the [i]th sample is at most its true time plus
    [E], plus [lead] for every credited chunk so far. *)
Definition P5 : Prop :=
  forall R, Meets R -> forall p I Sch n (truth : nat -> Z) E lead,
    let a := applied (run R p I Sch n) in
    0 <= lead ->
    (forall i e, nth_error a i = Some e -> reading e <= truth i + E) ->
    (forall i, truth i <= truth (S i)) ->
    (forall i e, nth_error a (S i) = Some e -> 0 < chunk e ->
       truth i + chunk e - lead <= truth (S i)) ->
    forall i e, nth_error a i = Some e ->
      lafter e <= truth i + E +
        lead * Z.of_nat (length (filter (fun e' => 0 <? chunk e') (firstn (S i) a))).

(** P6: [L] is an integer (it is a [Z]), at least the first sample, at most the largest
    applied sample plus the sum of credited chunks, and never above [max_safe]. *)
Definition P6 : Prop :=
  forall R, Meets R -> forall p I Sch n i e first,
    let a := applied (run R p I Sch n) in
    nth_error a 0 = Some first -> nth_error a i = Some e ->
    reading first <= lafter e /\
    lafter e <= fold_right Z.max (reading first) (map reading (firstn (S i) a)) +
                fold_right Z.add 0 (map chunk (firstn (S i) a)) /\
    lafter e <= max_safe.

(** P7: every result of an issued operation delivered to a fiber has an applied sample after
    the operation's last command and before the delivery. The second half of P7, about the
    host's reading at completion, is P4 under the host's own hypothesis, and has no separate
    statement. *)
Definition P7 : Prop :=
  forall R, Meets R -> forall p I Sch n pre f tok o post pre1 c k pre2,
    run R p I Sch n = pre ++ ADelivered f tok o :: post ->
    pre = pre1 ++ ACommand c k (Some (f, tok)) :: pre2 ->
    (forall c' k', ~ In (ACommand c' k' (Some (f, tok))) pre2) ->
    exists c' s l cr, In (ASampled c' s l cr) pre2.

(** P8: an issued operation cancelled while a fiber awaits it is followed by a sample, and
    its last command adds no floor; an operation cancelled before it is issued has no command
    and no sample. *)
Definition P8 : Prop :=
  (forall R, Meets R -> forall p I Sch n pre f tok post pre1 c k pre2,
     run R p I Sch n = pre ++ ACancelled f tok :: post ->
     pre = pre1 ++ ACommand c k (Some (f, tok)) :: pre2 ->
     (forall c' k', ~ In (ACommand c' k' (Some (f, tok))) pre2) ->
     (exists c' s l, In (ASampled c' s l None) pre2) /\ credits f tok pre2 = []) /\
  (forall R, Meets R -> forall p I Sch n pre f tok op post pre1 pre2,
     run R p I Sch n = pre ++ ACancelled f tok :: post ->
     pre = pre1 ++ AStart f tok op :: pre2 ->
     ~ starts f tok pre2 ->
     (forall c' k' o, ~ In (ACommand c' k' o) pre2) ->
     forall c' s l cr, ~ In (ASampled c' s l cr) pre2).

Definition S8 : Prop := P2 /\ P3 /\ P4 /\ P5 /\ P6 /\ P7 /\ P8 /\ P9.

(** ** S9. Agreement with revision 3's executor: refuted, kept on record

    S9 and S9_cancel below are false, and Rev3Counter.v proves their negations, together with
    those of the two earlier forms. By the owner's decision of 2026-11-22, S9 is not a theorem
    of the verification. With one fiber the executor differs from revision 3's in at least
    these ways, which is not a claim that they agree anywhere else:
    - a cancel signal that reaches a sample issues a replacement, where revision 3 records a
      defect ([rev3_cancel_during_sample_is_defect] in Witnesses.v);
    - an [L] above 2^53 - 1 is a violation ([overflow_separates_rev3] in Witnesses2.v);
    - after a violation the attempt closes and its finalizers run, where revision 3 stops
      ([rev3_clock_fin_runs] in Rev3Counter.v);
    - a release reported without an interruption leaves the slot held, where revision 3
      records a second operation ([rev3_spontaneous_diverges] in Rev3Counter.v);
    - a sleep longer than 2^31 - 1 ms is a chain, a priority other than 0 is a violation, a
      blocked root is a violation, and an infinite sleep is an endless chain (the dossier).
    With two fibers, a fiber still registered when the root exits makes the verdict
    [VDefect] ([rev3_masked_child_diverges] in Rev3Counter.v). *)

(** The actions attributed to a fiber other than the root. *)
Definition other_fiber (a : Action) : bool :=
  match a with
  | AStart f _ _ | ADelivered f _ _ | ACancelled f _ | ARefused f _ | AClock f _
  | ADraw f _ => negb (Nat.eqb f 0)
  | _ => false
  end.

(** The registrations a trace records. One fiber means one registration: the root's. *)
Definition registrations (t : list Action) : nat :=
  length (filter (fun a => match a with ARegister _ => true | _ => false end) t).

(** S9's conditions, read from this executor's trace, the inputs and the schedule: one
    fiber, counted by its registrations, no action by a fiber other than the root, no
    priority other than 0, no blocked root, no sleep that would become a chain, no
    foreign inputs; and, because revision 3's executor has none of these, no cut, a first
    attempt (nothing persisted), and no [L] above 2^53 - 1, which is a violation here and
    not under revision 3. #37's S9 was amended to match on 2026-11-22. *)
Definition s9_conditions (I : Inputs) (Sch : Schedule) (t : list Action) : Prop :=
  (registrations t <= 1)%nat /\
  forallb (fun a => negb (other_fiber a)) t = true /\
  ~ In (AViolation Priority) t /\ ~ In (AViolation Blocked) t /\
  ~ In (AViolation Overflow) t /\ cut_at Sch = None /\ persisted I = [] /\
  (forall f tok d, In (AStart f tok (OSleep d)) t ->
     exists m, d = Millis m /\ m <= max_chunk) /\
  (forall k, foreign I k = None).

(** Under the conditions and with no cancel signal, the two executors' traces agree. *)
Definition S9 : Prop :=
  forall R, Meets R -> forall p I Sch n1 n2,
    valid_schedule I Sch -> ~ In InCancel (entries I) ->
    s9_conditions I Sch (run R p I Sch n1) ->
    compatible (run R p I Sch n1) (run3 R p I Sch n2).

(** With a cancel signal, they agree except where it reaches a sample: there revision 3
    records a defect and this executor issues a replacement sample. A cancel signal that
    arrives while nothing is subscribed is covered by the first case. *)
Definition S9_cancel : Prop :=
  forall R, Meets R -> forall p I Sch n1 n2,
    valid_schedule I Sch -> s9_conditions I Sch (run R p I Sch n1) ->
    compatible (run R p I Sch n1) (run3 R p I Sch n2) \/
    exists pre c, prefix (pre ++ [ACommand c KSample None; AExit VDefect]) (run3 R p I Sch n2)
                  /\ compatible (pre ++ [ACommand c KSample None; ACommand (S c) KSample None])
                                (run R p I Sch n1).

(** ** S10. Draws per fiber *)

Definition draws_of (f : FiberId) (t : list Action) : list nat :=
  flat_map (fun a => match a with ADraw g r => if Nat.eqb f g then [r] else [] | _ => [] end) t.

Definition S10 : Prop :=
  forall R, Meets R -> forall p I Sch1 Sch2 r1 r2 n1 n2 f,
    valid_schedule I Sch1 -> valid_schedule I Sch2 ->
    requiv R r1 (init R p (seed I)) -> requiv R r2 (init R p (seed I)) ->
    compatible (draws_of f (before_cut (run_from R p I Sch1 r1 n1)))
               (draws_of f (before_cut (run_from R p I Sch2 r2 n2))).

(** ** S11. Subscriptions *)

(** The subscription is always the latest command issued, so a retired command is never
    subscribed again; a notification for a retired command changes no trace; and once
    closing has latched, the executor consumes no entry and issues no command. *)
Definition S11 : Prop :=
  (forall R p I Sch s sb, reachable R p I Sch s -> phase (xs s) = POpen ->
     sub (xs s) = Some sb -> S (sub_cmd sb) = next_cmd (xs s)) /\
  (forall R p I Sch s sb c r, reachable R p I Sch s -> quiet I Sch (xs s) ->
     queue (xs s) = [] -> phase (xs s) = POpen -> sub (xs s) = Some sb ->
     ~ (held (xs s) = true /\ waiter (xs s) <> None) ->
     (cursor (xs s) < arrived Sch (micro (xs s)))%nat ->
     nth_error (entries I) (cursor (xs s)) = Some (InNotify c r) -> c <> sub_cmd sb ->
     trace (xs (step R I Sch s)) = trace (xs s)) /\
  (forall R p I Sch s cut, reachable R p I Sch s -> phase (xs s) = PClosing cut ->
     let x' := xs (step R I Sch s) in
     cursor x' = cursor (xs s) /\
     exists suffix, trace x' = trace (xs s) ++ suffix /\ commands suffix = []).
