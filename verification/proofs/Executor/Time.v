(** * S8, the time rule: P2 to P9.

    P2, P4, P5 and P6 are proved in [TimeLClaims]; P3, P7, P8 and P9 in [TimeAClaims] from
    [time_fresh_tokens], which [TimeFresh3] proves from [Meets]. *)

From Durable Require Import Runtime Exec Rev3 Statements TimeBase TimeLClaims TimeAClaims
  TimeFresh3.

Theorem time_p3 : P3.
Proof. exact (time_p3_of time_fresh_tokens_hold). Qed.

Theorem time_p7 : P7.
Proof. exact (time_p7_of time_fresh_tokens_hold). Qed.

Theorem time_p8 : P8.
Proof. exact (time_p8_of time_fresh_tokens_hold). Qed.

Theorem time_p9 : P9.
Proof. exact (time_p9_of time_fresh_tokens_hold). Qed.

Theorem time_s8 : S8.
Proof.
  exact (conj time_p2 (conj time_p3 (conj time_p4 (conj time_p5 (conj time_p6
    (conj time_p7 (conj time_p8 time_p9))))))).
Qed.
