Require Import ZF.Class.Core.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.ImageByClass.

Export ZF.Notation.Image.

(* Direct image by a set f of a set a.                                          *)
Definition image (f a:U) : U := fromClass (toClass f) :[toClass a]:
  (Restrict.ImageIsSmall (toClass f) (toClass a) (SetIsSmall f)).

(* Notation "f :[ a ]:" := (image f a)                                          *)
Global Instance SetImage : Image U U := { image := image }.

(* The class of the image is the image by the class of the class.               *)
Proposition ToClass : forall (f a:U),
  toClass f:[a]: :~: (toClass f) :[toClass a]:.
Proof.
  intros F a. apply ToFromClass.
Qed.

(* The image by f of a is the image by the class of f of a.                     *)
Proposition ByClass : forall (f a:U), f:[a]: = (toClass f) :[a]:.
Proof.
  intros f a. apply EqualToClass.
  apply EquivTran with ((toClass f) :[toClass a]:).
  - apply ToClass.
  - apply EquivSym, ImageByClass.ToClassWhenSmall, SetIsSmall.
Qed.

Proposition Charac : forall (f a y:U),
  y :< f:[a]: <-> exists x, x :< a /\ :(x,y): :< f.
Proof.
  intros f a y. split; intros H1.
  - apply FromClass.Charac in H1. destruct H1 as [x [H1 H2]].
    exists x. split; assumption.
  - destruct H1 as [x [H1 H2]]. apply FromClass.Charac.
    exists x. split; assumption.
Qed.

(* The direct image is compatible with inclusion.                               *)
Proposition InclCompat : forall (f g a b:U),
  f :<=: g -> a :<=: b -> f:[a]: :<=: g:[b]:.
Proof.
  intros f g a b H1 H2 y H3. apply Charac in H3. destruct H3 as [x [H3 H4]].
  apply Charac. exists x. split.
  - apply H2. assumption.
  - apply H1. assumption.
Qed.

(* The direct image is left-compatible with inclusion.                          *)
Proposition InclCompatL : forall (f g a:U),
  f :<=: g -> f:[a]: :<=: g:[a]:.
Proof.
  intros f g a H1. apply InclCompat.
  - assumption.
  - apply InclRefl.
Qed.

(* The direct image is right-compatible with inclusion.                         *)
Proposition InclCompatR : forall (f a b:U),
  a :<=: b -> f:[a]: :<=: f:[b]:.
Proof.
  intros f a b H1. apply InclCompat.
  - apply InclRefl.
  - assumption.
Qed.

Proposition Inter2 : forall (f a b:U),
  f:[a :/\: b]: :<=: f:[a]: :/\: f:[b]:.
Proof.
  intros f a b y H1. apply Charac in H1. destruct H1 as [x [H1 H2]].
  apply Inter2.Charac in H1. destruct H1 as [H1 H3]. apply Inter2.Charac.
  split; apply Charac; exists x; split; assumption.
Qed.
