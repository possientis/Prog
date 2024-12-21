Declare Scope ZF_Binary_Image_scope.
Open    Scope ZF_Binary_Image_scope.

Require Import ZF.Binary.
Require Import ZF.Class.

(* Direct image of a class P by a binary class F.                               *)
Definition image (F:Binary) (P:Class) : Class := fun y =>
  exists x, P x /\ F x y.

Notation "F :[ P ]:" := (image F P)
  (at level 0, no associativity) : ZF_Binary_Image_scope.


