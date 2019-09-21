Require Import set.
Require Import Elem.

Open Scope set_scope.

(* This is the right definition of equality                                     *)
Definition equal (x y:set) : Prop :=
    (forall (z:set), z :: x <-> z :: y) 
 /\ (forall (z:set), x :: z <-> y :: z). 

Notation "x == y" := (equal x y) (at level 90) : set_scope.
