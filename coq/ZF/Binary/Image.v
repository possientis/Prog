Declare Scope ZF_Binary_Image_scope.
Open    Scope ZF_Binary_Image_scope.

Require Import ZF.Binary.
Require Import ZF.Class.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Image.
Require Import ZF.Set.

(* Direct image of a class P by a binary class F.                               *)
Definition image (F:Binary) (P:Class) : Class := fun y =>
  exists x, P x /\ F x y.

(* Notation "F :[ P ]:" := (image F P)                                          *)
Global Instance BinaryImage : Image Binary Class := { image := image }.

Proposition ImageCharac : forall (F:Binary) (P:Class) (y:U),
  F:[P]: y <-> exists x, P x /\ F x y.
Proof.
  intros F P y. split; intros H1.
  - unfold Core.Image.image, BinaryImage, image in H1. apply H1.
  - unfold Core.Image.image, BinaryImage, image. apply H1.
Qed.

(* The direct image is compatible with equivalences.                            *)
Proposition ImageEquivCompat : forall (F G:Binary) (P Q:Class),
  F :~: G -> P :~: Q -> F:[P]: :~: G:[Q]:.
Proof.
  intros F G P Q H1 H2 y. split; intros H3;
  apply (proj1 (ImageCharac _ _ _)) in H3; destruct H3 as [x [H3 H4]];
  apply ImageCharac; exists x; split.
    + apply H2. assumption.
    + apply H1. assumption.
    + apply H2. assumption.
    + apply H1. assumption.
Qed.

(* The direct image is left-compatible with equivalences.                       *)
Proposition ImageEquivCompatL : forall (F G:Binary) (P:Class),
  F :~: G -> F:[P]: :~: G:[P]:.
Proof.
  intros F G P H1. apply ImageEquivCompat.
  - assumption.
  - apply ClassEquivRefl.
Qed.

(* The direct image is right-compatible with equivalences.                      *)
Proposition ImageEquivCompatR : forall (F:Binary) (P Q:Class),
  P :~: Q -> F:[P]: :~: F:[Q]:.
Proof.
  intros F P Q H1. apply ImageEquivCompat.
  - apply BinaryEquivRefl.
  - assumption.
Qed.
