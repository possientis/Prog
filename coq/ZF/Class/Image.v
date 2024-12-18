Declare Scope ZF_Class_Image_scope.
Open Scope    ZF_Class_Image_scope.

Require Import ZF.Class.
Require Import ZF.Set.OrdPair.


(* Direct image of a class Q by a class P.                                      *)
Definition image (P Q:Class) : Class := fun y =>
  exists x, Q x /\ P :(x,y):.

Notation "P :[ Q ]:" := (image P Q)
  (at level 0, no associativity) : ZF_Class_Image_scope.
