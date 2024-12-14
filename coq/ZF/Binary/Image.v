Declare Scope ZF_Binary_Image_scope.
Open    Scope ZF_Binary_Image_scope.

Require Import ZF.Binary.
Require Import ZF.Class.
Require Import ZF.Set.

(* Direct image of a set a by a binary class F.                                 *)
Definition image (F:Binary) (a:U) : Class := fun y =>
  exists x, x :< a /\ F x y.

Notation "F :[ a ]:" := (image F a)
  (at level 0, no associativity) : ZF_Binary_Image_scope.


