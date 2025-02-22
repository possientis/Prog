Declare Scope ZF_Class_Image_scope.
Open Scope    ZF_Class_Image_scope.

Require Import ZF.Binary.Image.
Require Import ZF.Class.
Require Import ZF.Class.Empty.
Require Import ZF.Class.FromBinary.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.
Export ZF.Core.Image.

(* Direct image of a class Q by a class P.                                      *)
Definition image (P Q:Class) : Class := (toBinary P) :[Q]:.

(* Notation "P :[ Q ]:" := (image P Q)                                          *)
Global Instance ClassImage : Image Class Class := { image := image }.

Proposition ImageCharac : forall (P Q:Class) (y:U),
  P:[Q]: y <-> exists x, Q x /\ P :(x,y):.
Proof.
  intros P Q y. apply Binary.Image.ImageCharac.
Qed.

(* If P is functional and Q is small, then P:[Q]: is small.                     *)
Proposition ImageIsSmall : forall (P Q:Class),
  Functional P -> Small Q -> Small P :[Q]:.
Proof.
  intros P Q. apply Binary.Image.ImageIsSmall.
Qed.

(* The direct image is compatible with equivalences.                            *)
Proposition ImageEquivCompat : forall (P Q R S:Class),
  P :~: Q -> R :~: S -> P:[R]: :~: Q:[S]:.
Proof.
  intros P Q R S H1 H2 y. split; intros H3;
  apply (proj1 (ImageCharac _ _ _)) in H3; destruct H3 as [x [H3 H4]];
  apply ImageCharac; exists x; split.
  - apply H2. assumption.
  - apply H1. assumption.
  - apply H2. assumption.
  - apply H1. assumption.
Qed.

(* The direct image is left-compatible with equivalences.                       *)
Proposition ImageEquivCompatL : forall (P Q R:Class),
  P :~: Q -> P:[R]: :~: Q:[R]:.
Proof.
  intros P Q R H1. apply ImageEquivCompat.
  - assumption.
  - apply ClassEquivRefl.
Qed.

(* The direct image is right-compatible with equivalences.                      *)
Proposition ImageEquivCompatR : forall (P Q R:Class),
  P :~: Q -> R:[P]: :~: R:[Q]:.
Proof.
  intros P Q R H1. apply ImageEquivCompat.
  - apply ClassEquivRefl.
  - assumption.
Qed.

(* The direct image is compatible with inclusion.                               *)
Proposition ImageInclCompat : forall (P Q R S:Class),
  P :<=: Q -> R :<=: S -> P:[R]: :<=: Q:[S]:.
Proof.
  intros P Q R S H1 H2 y H3. unfold image in H3. destruct H3 as [x [H3 H4]].
  unfold image. exists x. split.
  - apply H2. assumption.
  - apply H1. assumption.
Qed.

(* The direct image is left-compatible with inclusion.                          *)
Proposition ImageInclCompatL : forall (P Q R:Class),
  P :<=: Q -> P:[R]: :<=: Q:[R]:.
Proof.
  intros P Q R H1. apply ImageInclCompat.
  - assumption.
  - apply InclRefl.
Qed.

(* The direct image is right-compatible with inclusion.                         *)
Proposition ImageInclCompatR : forall (P Q R:Class),
  P :<=: Q -> R:[P]: :<=: R:[Q]:.
Proof.
  intros P Q R H1. apply ImageInclCompat.
  - apply InclRefl.
  - assumption.
Qed.

Proposition ImageOfEmpty : forall (P Q:Class),
  Q :~: :0: -> P:[Q]: :~: :0:.
Proof.
  intros P Q H1 y. split; intros H2.
  - apply (proj1 (ImageCharac _ _ _)) in H2. destruct H2 as [x [H2 H3]].
    apply H1 in H2. apply EmptyCharac in H2. contradiction.
  - apply EmptyCharac in H2. contradiction.
Qed.
