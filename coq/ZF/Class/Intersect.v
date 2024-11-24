Declare Scope ZF_Class_Intersect_scope.
Open    Scope ZF_Class_Intersect_scope.

Require Import ZF.Class.Class.

(* The intersection of two classes P and Q.                                     *)
Definition intersect (P Q:Class) : Class := fun x => P x /\ Q x.

Notation "P :/\: Q" := (intersect P Q)
  (at level 4, left associativity) : ZF_Class_Intersect_scope.
