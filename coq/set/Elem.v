Require Import set.
Require Import subset.

Notation "{ x }" := (Cons x Nil) : set_scope.

Open Scope set_scope.

Definition elem (x y:set) : Prop := subset {x} y. 

Notation "x :: y" := (elem x y) : set_scope.

(*
Lemma elem_subset : forall (x y:set), 
    x <== y <-> forall (z:set), z :: x -> z :: y.
Proof.

Show.
*)
