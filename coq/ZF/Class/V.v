Require Import ZF.Class.Core.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Less.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Russell.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.OrdPair.

(* The class satisfied by all sets.                                             *)
Definition V : Class := fun _ => True.

(* Every class is a subclass of V.                                              *)
Proposition IsIncl : forall (A:Class), A :<=: V.
Proof.
  intros A x _. apply I.
Qed.

(* V is a left-identity for the binary intersection of classes.                 *)
Proposition Inter2VL : forall (P:Class),
  V :/\: P :~: P.
Proof.
  intros P x. split; intros H1.
  - apply H1.
  - split.
    + apply I.
    + assumption.
Qed.

(* V is a right-identity for the binary intersection of classes.                *)
Proposition Inter2VR : forall (P:Class),
  P :/\: V :~: P.
Proof.
  intros P x. split; intros H1.
  - apply H1.
  - split.
    + assumption.
    + apply I.
Qed.

(* V is a proper class.                                                         *)
Proposition IsProper : Proper V.
Proof.

  (* We need to show that the class of all sets is a proper class. *)
  assert (Proper V) as A. 2: apply A.

  (* Let us assume to the contrary that V is small. *)
  intros H1. assert (Small V) as A. { apply H1. } clear A.

  (* So there exists a set a such that x :< a <-> V x. *)
  assert (exists a, forall x, x :< a <-> V x) as A. { apply H1. } clear A.

  (* So let a be such a set. *)
  destruct H1 as [a H1].

  (* We obtain a contradiction by showing the set of all sets exists. *)
  apply Russell.

  (* So we need to show there is set of all sets. *)
  assert (exists a, forall x, x :< a) as A. 2: apply A.

  (* We claim that a is such a set. *)
  exists a.

  (* So given an arbitrary set x. *)
  intros x.

  (* We need to show that x belongs to a *)
  assert (x :< a) as A. 2: apply A.

  (* Which is clear. *)
  apply (H1 x), I.

Qed.

(* V^2 is a proper class.                                                       *)
Proposition V2IsProper : Proper (V :x: V).
Proof.
  apply SquareIsProper, IsProper.
Qed.

(* The product of two classes is a subclass of V^2.                             *)
Proposition ProdInclV2 : forall (P Q:Class),
  P :x: Q :<=: V :x: V.
Proof.
  intros P Q x H1. destruct H1 as [y [z [H1 [H2 H3]]]].
  exists y. exists z. split.
  - apply H1.
  - split; apply I.
Qed.

(* V^2 is a strict subclass of V.                                               *)
Proposition IsLess : V :x: V :<: V.
Proof.
  apply Less.Exists. split.
  - intros x H1. apply I.
  - exists :0:. split.
    + apply I.
    + intros [x [y [H1 _]]]. apply (OrdPairIsNotEmpty x y).
      symmetry. assumption.
Qed.

(* The intersection of the empty class is V.                                    *)
Proposition InterOfEmpty : :I(:0:) :~: V.
Proof.
  intros x. split; intros H1.
  - apply I.
  - intros y H2. contradiction.
Qed.
