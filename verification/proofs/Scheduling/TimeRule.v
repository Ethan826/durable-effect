(** * S8, the time rule, as the conjunction of its proved parts. *)

From Scheduling Require Import Statements SingleStep S8Upper.

Theorem s8 : S8.
Proof.
  exact (conj s8_monotone (conj s8_floor (conj s8_cancel (conj s8_chunks s8_upper)))).
Qed.
