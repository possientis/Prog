Require Import Arith. (* arith tactic DB *)

Ltac autoClear h := try (clear h; auto with arith; fail).

Ltac autoAfter tac := try(tac; auto with arith; fail).


Lemma example_use1: forall n p: nat, 
  n < p -> n <= p -> 0 < p -> S n < S p.
Proof.
  intros n p H H0 H1. autoAfter ltac:(clear H0 H1). (* clear H0 H1. auto with arith. *)
Qed.

Ltac le_S_star := apply le_n || (apply le_S; le_S_star). (* tactice is recursive *)


Theorem le_5_25: 5 <= 25.
Proof.
  le_S_star.  
Qed.
