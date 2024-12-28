Declare Scope ZF_Binary_Image_scope.
Open    Scope ZF_Binary_Image_scope.

Require Import ZF.Axiom.Replacement.
Require Import ZF.Binary.
Require Import ZF.Binary.Functional.
Require Import ZF.Class.
Require Import ZF.Class.Small.
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

(* If F is functional and P is small, then F:[P]: is small.                     *)
Proposition ImageIsSmall : forall (F:Binary) (P:Class),
  Functional F -> Small P -> Small F:[P]:.
Proof.

  (* Let F be a binary class and P be a class. *)
  intros F P.

  (* We assume that F is functional. *)
  intros H1. assert (Functional F) as A. { apply H1. } clear A.

  (* We assume that P is small. *)
  intros H2. assert (Small P) as A. { apply H2. } clear A.

  (* In particular P is equivalent to some set a. *)
  assert (exists a, toClass a :~: P) as H3. { apply (proj1 (SmallIsSomeSet _)), H2. }

  (* So let a be a set equivalent to the class P. *)
  destruct H3 as [a H3].

  (* We need to show that the direct image of P by F is small. *)
  assert (Small F:[P]:) as A. 2: apply A.

  (* The property of being small being compatible with equivalences... *)
  apply SmallEquivCompat with F:[toClass a]:.

  (* We first need to show the equivalence between F[a] and F[P]. *)
  - assert (F:[toClass a]: :~: F:[P]:) as A. 2: apply A.

  (* Which follows from the equivalence between a and P. *)
    apply ImageEquivCompatR, H3.

  (* We next need to show that F[a] is small. *)
  - assert (Small F:[toClass a]:) as A. 2: apply A.

  (* Which follows from the replacement axiom and the fact F is functional. *)
    apply Replacement, H1.
Qed.
