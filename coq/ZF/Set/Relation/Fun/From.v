Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Fun.From.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Relation.RestrictOfClass.

Require Import ZF.Notation.Eval.

Module CFF := ZF.Class.Relation.Fun.From.
Module SOR := ZF.Set.Relation.RestrictOfClass.


(* Given a set a and Coq expression f representing a function on sets, we aim   *)
(* to quickly define the associated function with domain a.                     *)
Definition from (a:U) (f:U -> U) : U := :[f]: :|: a.

Proposition Charac : forall (f:U -> U) (a x:U),
  x :< from a f <-> exists y, x = :(y,f y): /\ y :< a.
Proof.
  intros f a x. split; intros H1.
  - apply SOR.Charac in H1. 2: apply CFF.IsFunctional.
    destruct H1 as [y [z [H1 [H2 H3]]]].
    apply CFF.Charac2 in H3. subst. exists y. split. 2: assumption.
    reflexivity.
  - destruct H1 as [y [H1 H2]]. subst.
    apply SOR.Charac2Rev. 2: assumption.
    + apply CFF.IsFunctional.
    + apply CFF.Charac2. reflexivity.
Qed.

Proposition Charac2 : forall (f:U -> U) (a x y:U),
  :(x,y): :< from a f <-> x :< a /\ y = f x.
Proof.
  intros f a x y. split; intros H1.
  - apply Charac in H1. destruct H1 as [z [H1 H2]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3]. subst.
    split. 1: assumption. reflexivity.
  - destruct H1 as [H1 H2]. subst.
    apply Charac. exists x. split. 2: assumption. reflexivity.
Qed.

Proposition Satisfies : forall (f:U -> U) (a x:U),
  x :< a -> :(x,f x): :< from a f.
Proof.
  intros f a x H1. apply Charac2. split. 1: assumption. reflexivity.
Qed.

Proposition DomainOf : forall (f:U -> U) (a:U),
  domain (from a f) = a.
Proof.
  intros f a. apply Incl.DoubleInclusion. split; intros x H1.
  - apply Domain.Charac in H1. destruct H1 as [y H1].
    apply Charac2 in H1. apply H1.
  - apply Domain.Charac. exists (f x). apply Satisfies. assumption.
Qed.

Proposition IsRelation : forall (f:U -> U) (a:U), Relation (from a f).
Proof.
  intros f a x H1. apply Charac in H1. destruct H1 as [y [H1 H2]].
  exists y. exists (f y). assumption.
Qed.

Proposition IsFunctional : forall (f:U -> U) (a:U), Functional (from a f).
Proof.
  intros f a x y1 y2 H1 H2.
  apply Charac2 in H1. apply Charac2 in H2.
  destruct H1 as [_ H1]. destruct H2 as [_ H2]. subst. reflexivity.
Qed.

Proposition IsFunction : forall (f:U -> U) (a:U), Function (from a f).
Proof.
  intros f a. split.
  - apply IsRelation.
  - apply IsFunctional.
Qed.

Proposition IsFunctionOn : forall (f:U -> U) (a:U), FunctionOn (from a f) a.
Proof.
  intros f a. split.
  - apply IsFunction.
  - apply DomainOf.
Qed.

Proposition Eval : forall (f:U -> U) (a x:U),
  x :< a -> (from a f)!x = f x.
Proof.
  intros f a x H1. apply Eval.Charac.
  - apply IsFunctional.
  - rewrite DomainOf. assumption.
  - apply Satisfies. assumption.
Qed.
