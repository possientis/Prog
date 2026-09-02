Require Import Reals.

Open Scope R_scope.

Theorem example_for_field: forall x y:R, y <> 0 -> (x+y)/y = 1+(x/y).
Proof.
  intros x y H. field. exact H.
Qed.
