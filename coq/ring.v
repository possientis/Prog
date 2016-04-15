Require Import ZArith.
Open Scope Z_scope.

Theorem ring_example1: forall x y: Z, (x+y)*(x+y) = x*x + 2*x*y + y*y.
Proof.
  intros x y. ring.  
Qed.

Definition square (z:Z) := z*z.

Theorem ring_example2: forall x y:Z, square (x+y) = square x + 2*x*y + square y.
Proof.
  intros x y. unfold square. ring.
Qed.

Require Import Arith. (* otherwise ring tactic wil fail for nat *)

Theorem ring_example3: 
  (forall x y: nat, (x+y)*(x+y) = x*x + 2*x*y + y*y)%nat.
Proof.
  intros x y. ring.
Qed.
