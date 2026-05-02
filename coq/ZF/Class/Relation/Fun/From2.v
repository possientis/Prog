Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.


(* Given a Coq expression representing a function taking two sets as arguments  *)
(* define the class asociated with this expression and prove basic properties.  *)
Definition from2 (f:U -> U -> U) : Class := fun x => exists y z,
  x = :(:(y,z):,f y z):.

Proposition Charac2 : forall (f:U -> U -> U) (x y:U),
  from2 f :(x,y): <-> exists u v, x = :(u,v): /\ y = f u v.
Proof.
  intros f x y. split; intros [u [v H1]].
  - apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H2].
    exists u, v. split; assumption.
  - destruct H1 as [H1 H2]. exists u, v. rewrite H1, H2. reflexivity.
Qed.

Proposition Charac3 : forall (f:U -> U -> U) (x y z:U),
  from2 f :(:(x,y):,z): <-> z = f x y.
Proof.
  intros f x y z. split; intros H1.
  - apply Charac2 in H1. destruct H1 as [u [v [H1 H2]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3]. subst. reflexivity.
  - exists x, y. rewrite H1. reflexivity.
Qed.

Proposition Satisfies : forall (f:U -> U -> U) (a b:U),
  from2 f :(:(a,b):,f a b):.
Proof.
  intros f a b. apply Charac3. reflexivity.
Qed.

Proposition DomainOf : forall (f:U -> U -> U) (a b:U),
  domain (from2 f) :(a,b):.
Proof.
  intros f a b. exists (f a b). apply Satisfies.
Qed.

Proposition IsRelation : forall (f:U -> U -> U), Relation (from2 f).
Proof.
  intros f x H1. destruct H1 as [u [v H1]].
  exists :(u,v):, (f u v). assumption.
Qed.

Proposition IsFunctional : forall (f:U -> U -> U), Functional (from2 f).
Proof.
  intros f x y1 y2 H1 H2. apply Charac2 in H1. apply Charac2 in H2.
  destruct H1 as [u1 [v1 [H1 H3]]]. destruct H2 as [u2 [v2 [H2 H4]]].
  subst. apply OrdPair.WhenEqual in H2. destruct H2 as [H1 H2]. subst.
  reflexivity.
Qed.

Proposition IsFunction : forall (f:U -> U -> U), Function (from2 f).
Proof.
  intros f. split.
  - apply IsRelation.
  - apply IsFunctional.
Qed.

Proposition Eval : forall (f:U -> U -> U) (a b:U),
  ((from2 f)!:(a,b):) = f a b.
Proof.
  intros f a b. apply Function.Eval.
  - apply IsFunction.
  - apply Satisfies.
Qed.

