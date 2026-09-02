Require Import Arith. (* arith database for tactics *)

Theorem example_for_intuition: 
  forall n p q : nat, n <= p \/ n <= q -> n <= p \/ n <= S q.
Proof.
  intros n p q. intuition. (* auto with arith. will also work *)
Qed.

(* intuition = intuition auto with * *)
