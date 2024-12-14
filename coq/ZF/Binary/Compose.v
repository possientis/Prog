Declare Scope ZF_Binary_Compose_scope.
Open    Scope ZF_Binary_Compose_scope.

Require Import ZF.Binary.

(* Composition of two binary relation.                                          *)
Definition compose (G F:Binary) : Binary := fun x y =>
  exists z, F x z /\ G z y.

Notation "G :.: F" := (compose G F)
  (at level 11, right associativity) : ZF_Binary_Compose_scope.
