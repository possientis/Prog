Require Import ZArith.
Require Import Omega.

Open Scope Z_scope.

Theorem omega_example1: 
  forall x y z t:Z, x<=y<=z /\ z<=t<=x -> x = t.
Proof.
  intros x y z t H. omega.
Qed.

Definition square (z:Z) := z*z.

(* omega needs linear goals and context *)
(* but getting away with it here *)
Theorem omega_example2:
  forall x y:Z, 
  0 <= square x -> 3*square x <= 2*y -> square x <= y.
Proof.
  intros x y H H'. omega.
Qed.

Theorem omega_example3:
  forall x y:Z,
  0 <= x*x ->  3*(x*x) <= 2*y -> x*x <= y.
Proof.
  intros x y H H'. omega.
Qed.

(* omega cannot convert this into linear problem *)
(* it needs to apply associativity of mult which it *)
(* is not programmed to do *)

Theorem omega_example4:
  forall x y:Z,
  0 <= x*x -> (3*x)*x <= 2*y -> x*x <= y.
Proof.
  intros x y H H'. (* omega failing here *)
Abort.



