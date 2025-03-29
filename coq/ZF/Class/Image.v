Require Import ZF.Class.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Replacement.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

Require Import ZF.Core.Image.
Export ZF.Core.Image.

(* Direct image of a class Q by a class P.                                      *)
Definition image (F A:Class) : Class := fun y =>
  exists x, A x /\ F :(x,y):.

(* Notation "F :[ A ]:" := (image F A)                                          *)
Global Instance ClassImage : Image Class Class := { image := image }.

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
  - apply Class.EquivRefl.
Qed.

(* The direct image is right-compatible with equivalences.                      *)
Proposition ImageEquivCompatR : forall (P Q R:Class),
  P :~: Q -> R:[P]: :~: R:[Q]:.
Proof.
  intros P Q R H1. apply ImageEquivCompat.
  - apply Class.EquivRefl.
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

(* If F is functional and P is small, then F:[P]: is small.                     *)
Proposition ImageIsSmall : forall (F P:Class),
  Functional F -> Small P -> Small F :[P]:.
Proof.

  (* Let F and P be two arbitrary classes. *)
  intros F P.

  (* We assume that F is functional. *)
  intros H1. assert (Functional F) as A. { apply H1. } clear A.

  (* We assume that P is small. *)
  intros H2. assert (Small P) as A. { apply H2. } clear A.

  (* In particular P is equivalent to some set a. *)
  assert (exists a, toClass a :~: P) as H3. { assumption. }

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

  (* Which follows from replacement and the fact F is functional. *)
    apply Replacement, H1.
Qed.
