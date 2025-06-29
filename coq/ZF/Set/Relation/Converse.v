Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.

Export ZF.Notation.Inverse.

(* The converse of a set.                                                       *)
Definition converse (f:U) : U := fromClass (toClass f)^:-1:
  (Converse.IsSmall (toClass f) (SetIsSmall f)).

(* Notation "f ^:-1:" := (converse f)                                           *)
Global Instance SetInverse : Inverse U := { inverse := converse }.

(* The class of the converse is the converse of the class.                      *)
Proposition ToClass : forall (f:U),
  toClass f^:-1: :~: (toClass f)^:-1:.
Proof.
  intros f. apply ToFromClass.
Qed.

Proposition Charac : forall (f x:U),
  x :< f^:-1: <-> exists y z, x = :(z,y): /\ :(y,z): :< f.
Proof.
  intros f x. split; intros H1.
  - apply FromClass.Charac in H1. destruct H1 as [y [z [H1 H2]]].
    exists y. exists z. split; assumption.
  - destruct H1 as [y [z [H1 H2]]]. apply FromClass.Charac.
    exists y. exists z. split; assumption.
Qed.

Proposition Charac2 : forall (f y z:U),
  :(y,z): :< f^:-1: -> :(z,y): :< f.
Proof.
  intros f y z H1. apply Charac in H1. destruct H1 as [z' [y' [H1 H2]]].
  apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3]. subst. assumption.
Qed.

Proposition Charac2Rev : forall (f y z:U),
  :(z,y): :< f -> :(y,z): :< f^:-1:.
Proof.
  intros f y z H1. apply Charac. exists z. exists y. split.
  1: reflexivity. assumption.
Qed.

(* The converse operation is compatible with set inclusion.                     *)
Proposition InclCompat : forall (f g:U),
  f :<=: g -> f^:-1: :<=: g^:-1:.
Proof.
  intros  f g H1 x H2.
  apply Charac in H2. destruct H2 as [y [z [H2 H3]]]. subst. apply Charac.
  exists y. exists z. split. 1: reflexivity. apply H1. assumption.
Qed.

(* The converse of a set if a relation.                                         *)
Proposition IsRelation : forall (f:U), Relation f^:-1:.
Proof.
  intros f x H1. apply Charac in H1. destruct H1 as [y [z [H1 H2]]].
  exists z. exists y. assumption.
Qed.

(* The converse of the converse is a subset of the original set.                *)
Proposition IsIncl : forall (f:U),
  (f^:-1:)^:-1: :<=: f.
Proof.
  intros f x H1. apply Charac in H1. destruct H1 as [y [z [H1 H2]]].
  apply Charac2 in H2. subst. assumption.
Qed.

(* A set is a relation iff the converse acting on it is idempotent.           *)
Proposition IsIdempotent : forall (f:U),
  Relation f <-> (f^:-1:)^:-1: = f.
Proof.
  intros f. split; intros H1.
  - apply DoubleInclusion. split; intros x H2.
    + specialize (H1 x). apply Charac in H2. destruct H2 as [z [y [H2 H3]]].
      apply Charac2 in H3. subst. assumption.
    + specialize (H1 x H2). destruct H1 as [y [z H1]]. subst.
      apply Charac2Rev, Charac2Rev. assumption.
  - rewrite <- H1. apply IsRelation.
Qed.

(* The domain of the converse is the range.                                     *)
Proposition Domain : forall (f:U),
  domain f^:-1: = range f.
Proof.
  intros f. apply DoubleInclusion. split; intros y H1.
  - apply Domain.Charac in H1. destruct H1 as [x H1]. apply Charac2 in H1.
    apply Range.Charac. exists x. assumption.
  - apply Range.Charac in H1. destruct H1 as [x H1].
    apply Domain.Charac. exists x. apply Charac2Rev. assumption.
Qed.

(* The range of the converse is the domain.                                     *)
Proposition Range : forall (f:U),
  range f^:-1: = domain f.
Proof.
  intros f. apply DoubleInclusion. split; intros x H1.
  - apply Range.Charac in H1. destruct H1 as [y H1]. apply Charac2 in H1.
    apply Domain.Charac. exists y. assumption.
  - apply Domain.Charac in H1. destruct H1 as [y H1].
    apply Range.Charac. exists y. apply Charac2Rev. assumption.
Qed.

Proposition WhenFunctional : forall (f x y z:U),
  Functional f^:-1: -> :(x,z): :< f -> :(y,z): :< f -> x = y.
Proof.
  intros f x y z H1 H2 H3. apply H1 with z; apply Charac2Rev; assumption.
Qed.

Proposition Inter2Image : forall (f a b:U), Functional f^:-1: ->
  f:[a :/\: b]: = f:[a]: :/\: f:[b]:.
Proof.
  intros f a b H1. apply DoubleInclusion. split.
  - apply Image.Inter2.
  - intros y H2. apply Inter2.Charac in H2. destruct H2 as [H2 H3].
    apply Image.Charac in H2. apply Image.Charac in H3.
    destruct H2 as [x1 [H2 H4]]. destruct H3 as [x2 [H3 H5]].
    assert (x1 = x2) as H6. { apply WhenFunctional with f y; assumption. }
    subst. apply Image.Charac. exists x2. split. 2: assumption.
    apply Inter2.Charac. split; assumption.
Qed.
