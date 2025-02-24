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
Definition image (F A:Class) : Class := fun y =>
  exists x, A x /\ F :(x,y):.

(* Notation "F :[ A ]:" := (image F A)                                          *)
Global Instance ClassImage : Image Class Class := { image := image }.

(* Viewing the class F as a binary relation does not change images.             *)
Proposition ImageFromBinary : forall (F A:Class),
  F:[A]: :~: (toBinary F) :[A]:.
Proof.
  intros F A y. split; intros H1; destruct H1 as [x [H1 H2]];
  exists x; split; assumption.
Qed.

(* If F is functional and A is small, then F:[A]: is small.                     *)
Proposition FunctionalImageIsSmall : forall (F A:Class),
  Functional F -> Small A -> Small F :[A]:.
Proof.
  intros F A H1 H2. apply SmallEquivCompat with ((toBinary F) :[A]:).
  - apply ClassEquivSym, ImageFromBinary.
  - apply Binary.Image.ImageIsSmall. 2: assumption.
    apply (proj1 (FunctionalFromBinary _)). assumption.
Qed.

(* The direct image is compatible with equivalences.                            *)
Proposition ImageEquivCompat : forall (P Q R S:Class),
  P :~: Q -> R :~: S -> P:[R]: :~: Q:[S]:.
Proof.
  intros P Q R S H1 H2 y. split; intros H3;
  destruct H3 as [x [H3 H4]]; exists x; split.
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
  - destruct H2 as [x [H2 H3]]. apply H1 in H2. apply EmptyCharac in H2. contradiction.
  - apply EmptyCharac in H2. contradiction.
Qed.

