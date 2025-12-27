Declare Scope ZF_Class_ToFun_scope.
Open    Scope ZF_Class_ToFun_scope.

Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

Require Import ZF.Notation.Eval.

(* Given a Coq expression representing a function on sets, we aim to quickly    *)
(* define the class asociated with this expression and prove basic properties.  *)
Definition toFun (f:U -> U) : Class := fun x => exists y, x = :(y,f y):.

Notation ":[ f ]:" := (toFun f) (at level 1) : ZF_Class_ToFun_scope.

Proposition Charac2 : forall (f:U -> U) (x y:U),
  :[f]: :(x,y): <-> y = f x.
Proof.
  intros f x y. split; intros H1.
  - destruct H1 as [x' H1]. apply OrdPair.WhenEqual in H1.
    destruct H1 as [H1 H2]. subst. reflexivity.
  - exists x. subst. reflexivity.
Qed.

Proposition Satisfies : forall (f:U -> U) (a:U),
  :[f]: :(a, f a):.
Proof.
  intros f x. apply Charac2. reflexivity.
Qed.

Proposition DomainOf : forall (f:U -> U) (a:U), domain :[f]: a.
Proof.
  intros f a. exists (f a). apply Satisfies.
Qed.

Proposition IsRelation : forall (f:U -> U), Relation :[f]:.
Proof.
  intros f x H1. destruct H1 as [y H1]. subst. exists y. exists (f y).
  reflexivity.
Qed.

Proposition IsFunctional : forall (f:U -> U), Functional :[f]:.
Proof.
  intros f x y1 y2 H1 H2. apply Charac2 in H1. apply Charac2 in H2.
  subst. reflexivity.
Qed.

Proposition IsFunction : forall (f:U -> U), Function :[f]:.
Proof.
  intros f. split.
  - apply IsRelation.
  - apply IsFunctional.
Qed.

Proposition Eval : forall (f:U -> U) (a:U),
  :[f]:!a = f a.
Proof.
  intros f a. apply EvalOfClass.Charac.
  - apply IsFunctional.
  - apply DomainOf.
  - apply Satisfies.
Qed.
