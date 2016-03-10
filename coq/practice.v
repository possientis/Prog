Require Import Arith ZArith.
Open Scope nat_scope.

Check le.
Check lt.
Print lt. (* lt = fun n m : nat => S n <= m : nat -> nat -> Prop *)

Theorem conv_example : forall n:nat, 7*5 < n -> 6*6 <= n.
Proof.
  intros n H.
  exact H. (* the tactic 'exact' will succeed provided type conversion is possible *)
  (* the same it true of 'assumption' *)
Qed.
(* although the terms 7*5 < n and 6*6 <= n are different, following delta , iota and beta reductions, both terms are reduced to 36 <= n and consequently 
the tactics 'exact H' or 'assumption' will succeed *)
