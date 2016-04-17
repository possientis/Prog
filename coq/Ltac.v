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

Section primes.

Definition divides (n m:nat) := exists p:nat, p*n = m.

Hypotheses
  (divides_0 : forall n:nat, divides n 0)
  (divides_plus : forall n m:nat, divides n m -> divides n (n+m))
  (not_divides_plus : forall n m:nat, ~divides n m -> ~divides n (n+m))
  (not_divides_lt : forall n m:nat, 0 < m -> m < n -> ~divides n m)
  (not_lt_2_divides: forall n m:nat, n <> 1 -> n < 2 -> 0 < m -> ~divides n m)
  (le_plus_minus : forall n m: nat, le n m -> m = n + (m-n))
  (lt_lt_or_eq  : forall n m:nat, n < S m -> n < m \/ n=m).

Ltac check_not_divides :=
  match goal with
    | [ |- (~divides ?X1 ?X2) ] => 
        cut (X1 <= X2); [idtac | le_S_star]; intros Hle;
        rewrite (le_plus_minus _ _ Hle); apply not_divides_plus;
        simpl; clear Hle; check_not_divides (* recursive call *)
    | [ |- _ ]                  => apply not_divides_lt; unfold lt; le_S_star
  end.

Lemma check1: ~divides 34 45.
Proof.
  match goal with
    | [ |- (~divides ?X1 ?X2) ] =>
      cut(X1 <= X2); [idtac | le_S_star]; intro Hle; rewrite (le_plus_minus _ _ Hle);
    apply not_divides_plus; simpl; clear Hle; check_not_divides
    | [  |- _]                  =>
      apply not_divides_lt; unfold lt; le_S_star 
  end.
Qed.


Lemma check2: ~divides 34 45.
Proof.
  check_not_divides.
Qed.




  


