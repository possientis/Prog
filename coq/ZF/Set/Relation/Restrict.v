Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Restrict.
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

Export ZF.Notation.Pipe.

(* Restricting a set f to a set a.                                              *)
Definition restrict (f a:U) : U := fromClass (toClass f :|: toClass a)
  (Restrict.IsSmall' (toClass f) (toClass a) (SetIsSmall f)).

(* Notation "f :|: a" := (restrict f a)                                         *)
Global Instance SetPipe : Pipe U U := { pipe := restrict }.

Proposition ToClass : forall (f a:U),
  toClass (f:|:a) :~: toClass f :|: toClass a.
Proof.
  intros f a. apply ToFromClass.
Qed.

Proposition Charac : forall (f a x:U),
  x :< f:|:a <-> exists y z, x = :(y,z): /\ y :< a /\ :(y,z): :< f.
Proof.
  intros f a x. split; intros H1.
  - apply FromClass.Charac in H1. destruct H1 as [y [z [H1 [H2 H3]]]].
    exists y. exists z. split. 1: assumption. split; assumption.
  - destruct H1 as [y [z [H1 [H2 H3]]]]. apply FromClass.Charac.
    exists y. exists z. split. 1: assumption. split; assumption.
Qed.

Proposition Charac2 : forall (f a y z:U),
  :(y,z): :< (f:|:a) <-> y :< a /\ :(y,z): :< f.
Proof.
  intros f a y z. split; intros H1.
  - apply Charac in H1. destruct H1 as [y' [z' [H1 H2]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H4].
    subst. assumption.
  - apply Charac. exists y. exists z. split.
    + reflexivity.
    + assumption.
Qed.

(* The restriction is always a relation.                                        *)
Proposition IsRelation : forall (f a:U), Relation (f:|:a).
Proof.
  intros f a x H1. apply Charac in H1. destruct H1 as [y [z [H1 _]]].
  exists y. exists z. assumption.
Qed.

(* The restriction of a functional set is functional.                           *)
Proposition IsFunctional : forall (f a:U),
  Functional f -> Functional (f:|:a).
Proof.
  intros f a H1 x y z H2 H3.
  apply Charac2 in H2. destruct H2 as [_ H2].
  apply Charac2 in H3. destruct H3 as [_ H3].
  apply H1 with x; assumption.
Qed.

(* The domain of the restriction f|a is the intersection of a and domain f.     *)
Proposition DomainOf : forall (f a:U),
  domain (f:|:a) = a :/\: domain f.
Proof.
  intros f a. apply DoubleInclusion. split; intros x H1.
  - apply Domain.Charac in H1. destruct H1 as [y H1].
    apply Charac2 in H1. destruct H1 as [H1 H2].
    apply Inter2.Charac. split. 1: assumption.
    apply Domain.Charac. exists y. assumption.
  - apply Inter2.Charac in H1. destruct H1 as [H1 H2].
    apply Domain.Charac in H2. destruct H2 as [y H2].
    apply Domain.Charac. exists y. apply Charac2. split; assumption.
Qed.

(* The direct image by f of a is the range of the restriction f|a.              *)
Proposition ImageIsRange : forall (f a:U),
  f:[a]: = range (f:|:a).
Proof.
  intros f a. apply DoubleInclusion. split; intros y H1.
  - apply Image.Charac in H1. destruct H1 as [x [H1 H2]].
    apply Range.Charac. exists x. apply Charac2. split; assumption.
  - apply Range.Charac in H1. destruct H1 as [x H1].
    apply Charac2 in H1. destruct H1 as [H1 H2].
    apply Image.Charac. exists x. split; assumption.
Qed.

(* A restriction is a subset of the original set.                               *)
Proposition IsIncl : forall (f a:U),
  f:|:a :<=: f.
Proof.
  intros f a x H1. apply Charac in H1. destruct H1 as [y [z [H1 [_ H2]]]].
  subst. assumption.
Admitted.
