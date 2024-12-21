Declare Scope ZF_Binary_Image_scope.
Open    Scope ZF_Binary_Image_scope.

Require Import ZF.Binary.
Require Import ZF.Class.
Require Import ZF.Core.Image.

(* Direct image of a class P by a binary class F.                               *)
Definition image (F:Binary) (P:Class) : Class := fun y =>
  exists x, P x /\ F x y.

(* Notation "F :[ P ]:" := (image F P)                                          *)
Global Instance BinaryImage : Image Binary Class := { image := image }.

