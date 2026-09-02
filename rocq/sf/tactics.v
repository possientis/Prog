Require Import nat.

Definition add1 : nat -> nat.
    intros n. apply S. apply n.
Defined.

(*
Compute add1 2.
*)

