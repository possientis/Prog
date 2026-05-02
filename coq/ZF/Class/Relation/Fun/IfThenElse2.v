Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

Require Import ZF.Notation.Eval.

(* Given Coq expressions f1 and f2 representing two variables functions on sets *)
(* and a class A we aim to quickly define the function class F such that:       *)
(* F(y,z) = f1(y,z) if   A (y,z)                                                *)
(* F(y,z) = f2(y,z) if ~ A (y,z)                                                *)
Definition ifThenElse2 (A:Class) (f1 f2:U*U -> U) : Class := fun x => exists y z,
  x = :(:(y,z):,f1 (y,z)): /\   A :(y,z):   \/
  x = :(:(y,z):,f2 (y,z)): /\ ~ A :(y,z):.

(* Membership of a pair in ifThenElse2 exposes the key witnesses and branch.    *)
Proposition Charac2 : forall (A:Class) (f1 f2:U*U -> U) (x y:U),
  ifThenElse2 A f1 f2 :(x,y): <->
  exists u v, x = :(u,v): /\
    (y = f1 (u,v) /\   A :(u,v):  \/
     y = f2 (u,v) /\ ~ A :(u,v):).
Proof.
  (* Proof by Claude.                                                           *)
  intros A f1 f2 x y. split.
  - intros [u [v [[H1 H2]|[H1 H2]]]].
    + apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3]. subst.
      exists u, v. split. 1: reflexivity. left.  split. 2: assumption.
      reflexivity.
    + apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3]. subst.
      exists u, v. split. 1: reflexivity. right. split. 2: assumption.
      reflexivity.
  - intros [u [v [H1 [[H2 H3]|[H2 H3]]]]]; subst; exists u, v.
    + left.  split. 2: assumption. reflexivity.
    + right. split. 2: assumption. reflexivity.
Qed.

(* Membership at a fully explicit input pair reduces to the two-branch choice.  *)
Proposition Charac3 : forall (A:Class) (f1 f2:U*U -> U) (x y z:U),
  ifThenElse2 A f1 f2 :(:(x,y):,z): <->
  z = f1 (x,y) /\   A :(x,y):  \/
  z = f2 (x,y) /\ ~ A :(x,y):.
Proof.
  (* Proof by Claude.                                                           *)
  intros A f1 f2 x y z. split.
  - intros H1. apply Charac2 in H1. destruct H1 as [u [v [H1 H2]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [Hu Hv]. subst. exact H2.
  - intros H1. apply Charac2. exists x, y. split. 1: reflexivity. exact H1.
Qed.

(* When the condition holds, the first-branch value belongs to ifThenElse2.     *)
Proposition Satisfies1 : forall (A:Class) (f1 f2:U*U -> U) (a b:U),
  A :(a,b): -> ifThenElse2 A f1 f2 :(:(a,b):,f1 (a,b)):.
Proof.
  (* Proof by Claude.                                                           *)
  intros A f1 f2 a b H1. apply Charac3. left. split. 2: assumption. reflexivity.
Qed.

(* When the condition fails, the second-branch value belongs to ifThenElse2.    *)
Proposition Satisfies2 : forall (A:Class) (f1 f2:U*U -> U) (a b:U),
  ~ A :(a,b): -> ifThenElse2 A f1 f2 :(:(a,b):,f2 (a,b)):.
Proof.
  (* Proof by Claude.                                                           *)
  intros A f1 f2 a b H1. apply Charac3. right. split. 2: assumption. reflexivity.
Qed.

(* Every pair of sets lies in the domain of ifThenElse2.                        *)
Proposition DomainOf : forall (A:Class) (f1 f2:U*U -> U) (a b:U),
  domain (ifThenElse2 A f1 f2) :(a,b):.
Proof.
  (* Proof by Claude.                                                           *)
  intros A f1 f2 a b.
  assert (A :(a,b): \/ ~ A :(a,b):) as [H1|H1]. { apply LawExcludedMiddle. }
  - exists (f1 (a,b)). apply Satisfies1. assumption.
  - exists (f2 (a,b)). apply Satisfies2. assumption.
Qed.

(* ifThenElse2 is a relation: every member is an ordered pair.                  *)
Proposition IsRelation : forall (A:Class) (f1 f2:U*U -> U),
  Relation (ifThenElse2 A f1 f2).
Proof.
  (* Proof by Claude.                                                           *)
  intros A f1 f2 x H1. destruct H1 as [y [z [[H1 H2]|[H1 H2]]]]; subst.
  - exists :(y,z):, (f1 (y,z)). reflexivity.
  - exists :(y,z):, (f2 (y,z)). reflexivity.
Qed.

(* ifThenElse2 is functional: the condition uniquely determines the output.     *)
Proposition IsFunctional : forall (A:Class) (f1 f2:U*U -> U),
  Functional (ifThenElse2 A f1 f2).
Proof.
  (* Proof by Claude.                                                           *)
  intros A f1 f2 x y1 y2 H1 H2.
  apply Charac2 in H1. destruct H1 as [u1 [v1 [Hx H1]]].
  apply Charac2 in H2. destruct H2 as [u2 [v2 [Hx' H2]]].
  rewrite Hx in Hx'. apply OrdPair.WhenEqual in Hx'.
  destruct Hx' as [Hu Hv]. subst.
  destruct H1 as [[H1 H3]|[H1 H3]]; destruct H2 as [[H2 H4]|[H2 H4]];
  try contradiction; subst; reflexivity.
Qed.

(* ifThenElse2 is a function: it is both a relation and functional.             *)
Proposition IsFunction : forall (A:Class) (f1 f2:U*U -> U),
  Function (ifThenElse2 A f1 f2).
Proof.
  intros A f1 f2. split.
  - apply IsRelation.
  - apply IsFunctional.
Qed.

(* When the condition holds, evaluating ifThenElse2 returns the first branch.   *)
Proposition Eval1 : forall (A:Class) (f1 f2:U*U -> U) (a b:U),
  A :(a,b): -> ((ifThenElse2 A f1 f2)!:(a,b):) = f1 (a,b).
Proof.
  (* Proof by Claude.                                                           *)
  intros A f1 f2 a b H1. apply Function.Eval.
  - apply IsFunction.
  - apply Satisfies1. assumption.
Qed.

(* When the condition fails, evaluating ifThenElse2 returns the second branch.  *)
Proposition Eval2 : forall (A:Class) (f1 f2:U*U -> U) (a b:U),
  ~ A :(a,b): -> ((ifThenElse2 A f1 f2)!:(a,b):) = f2 (a,b).
Proof.
  (* Proof by Claude.                                                           *)
  intros A f1 f2 a b H1. apply Function.Eval.
  - apply IsFunction.
  - apply Satisfies2. assumption.
Qed.
