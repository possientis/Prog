Declare Scope ZF_Class_Image_scope.

Require Import ZF.Class.
Require Import ZF.Set.
Require Import ZF.Binary.Image.
Require Import ZF.Class.Binary.
Require Import ZF.Set.OrdPair.

Open Scope    ZF_Class_Image_scope.

(* Direct image of a set by a class P.                                          *)
Definition image (P:Class) (a:U) : Class := Image.image (toBinary P) a.

Notation "P :[ a ]:" := (image P a)
  (at level 0, no associativity) : ZF_Class_Image_scope.

Proposition ImageCharac : forall (P:Class) (a y:U),
  P:[a]: y -> exists x, x :< a /\ P :(x,y):.
Proof.
  intros P a y H1. apply H1.
Qed.
