Declare Scope ZF_Intersect_scope.
Open    Scope ZF_Intersect_scope.

Require Import Logic.ZF.Core.
Require Import Logic.ZF.Comprehension.

(* The intersection of two sets a and b.                                        *)
Definition intersect (a b:U) : U := :{ a | fun x => x :< b }:.

Notation "a :/\: b" := (intersect a b)
  (at level 3, left associativity) : ZF_Intersect_scope.

