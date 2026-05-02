Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Fun.IfThenElse2.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Relation.RestrictOfClass.

Require Import ZF.Notation.Eval.

Module CFI2 := ZF.Class.Relation.Fun.IfThenElse2.
Module SOR  := ZF.Set.Relation.RestrictOfClass.

(* The function defined on a x b by:                                            *)
(* f(u,v) = f1(u,v) if the condition holds at (u,v)                            *)
(* f(u,v) = f2(u,v) if the condition fails at (u,v)                            *)
Definition ifThenElse2 (a b:U) (A:Class) (f1 f2:U -> U -> U) : U
  := (CFI2.ifThenElse2 A f1 f2) :|: (a :x: b).

(* Generic membership exposes pair witnesses and the applicable branch.         *)
Proposition Charac : forall (A:Class) (f1 f2:U -> U -> U) (a b x:U),
  x :< ifThenElse2 a b A f1 f2 <-> exists u v,
    x = :(:(u,v):,f1 u v): /\ u :< a /\ v :< b /\   A :(u,v):  \/
    x = :(:(u,v):,f2 u v): /\ u :< a /\ v :< b /\ ~ A :(u,v):.
Proof.
  (* Proof by Claude.                                                           *)
  (* An element is a pair with first component in the product, and second       *)
  (* component determined by the branch condition on the first component.       *)
  intros A f1 f2 a b x. split; intros H1.
  - apply SOR.Charac in H1. 2: apply CFI2.IsFunctional.
    destruct H1 as [y [z [H1 [H2 H3]]]].
    apply Prod.Charac in H2. destruct H2 as [u [v [H2 [H4 H5]]]]. subst y.
    apply CFI2.Charac3 in H3.
    destruct H3 as [[H3 H6]|[H3 H6]]; subst z; exists u, v.
    + left.  split. 1: assumption. split. 1: assumption. split; assumption.
    + right. split. 1: assumption. split. 1: assumption. split; assumption.
  - destruct H1 as [u [v [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]]]]; subst.
    + apply SOR.Charac2Rev.
      * apply CFI2.IsFunctional.
      * apply Prod.Charac. exists u, v. split. 1: reflexivity. split; assumption.
      * apply CFI2.Satisfies1. assumption.
    + apply SOR.Charac2Rev.
      * apply CFI2.IsFunctional.
      * apply Prod.Charac. exists u, v. split. 1: reflexivity. split; assumption.
      * apply CFI2.Satisfies2. assumption.
Qed.

(* Membership of a pair exposes the pair witnesses and applicable branch.       *)
Proposition Charac2 : forall (A:Class) (f1 f2:U -> U -> U) (a b p q:U),
  :(p,q): :< ifThenElse2 a b A f1 f2 <->
  exists u v, p = :(u,v): /\ u :< a /\ v :< b /\
    (q = f1 u v /\   A :(u,v):  \/
     q = f2 u v /\ ~ A :(u,v):).
Proof.
  (* Proof by Claude.                                                           *)
  (* Pair membership unpacks the witnesses via ordered-pair injectivity.        *)
  intros A f1 f2 a b p q. split; intros H1.
  - apply Charac in H1.
    destruct H1 as [u [v [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]]]].
    + apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H5].
      exists u, v. split. 1: assumption. split. 1: assumption.
      split. 1: assumption. left. split; assumption.
    + apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H5].
      exists u, v. split. 1: assumption. split. 1: assumption.
      split. 1: assumption. right. split; assumption.
  - destruct H1 as [u [v [H1 [H2 [H3 [[H4 H5]|[H4 H5]]]]]]].
    + subst p. subst q. apply Charac. exists u, v. left.
      split. 1: reflexivity. split. 1: assumption. split; assumption.
    + subst p. subst q. apply Charac. exists u, v. right.
      split. 1: reflexivity. split. 1: assumption. split; assumption.
Qed.

(* Membership at a fully explicit input reduces to the two branch conditions.   *)
Proposition Charac3 : forall (A:Class) (f1 f2:U -> U -> U) (a b u v w:U),
  :(:(u,v):,w): :< ifThenElse2 a b A f1 f2 <->
  u :< a /\ v :< b /\
    (w = f1 u v /\   A :(u,v):  \/
     w = f2 u v /\ ~ A :(u,v):).
Proof.
  (* Proof by Claude.                                                           *)
  (* Follows from the pair characterization via ordered-pair injectivity.       *)
  intros A f1 f2 a b u v w. split; intros H1.
  - apply Charac2 in H1. destruct H1 as [u' [v' [H1 [H2 [H3 H4]]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [Hu Hv]. subst u'. subst v'.
    split. 1: assumption. split. 1: assumption. assumption.
  - destruct H1 as [H1 [H2 H3]]. apply Charac2.
    exists u, v. split. 1: reflexivity. split. 1: assumption.
    split. 1: assumption. assumption.
Qed.

(* The first branch value belongs to ifThenElse2 when the condition holds.      *)
Proposition Satisfies1 : forall (A:Class) (f1 f2:U -> U -> U) (a b u v:U),
  u :< a -> v :< b -> A :(u,v): ->
  :(:(u,v):,f1 u v): :< ifThenElse2 a b A f1 f2.
Proof.
  (* Proof by Claude.                                                           *)
  (* Follows directly from the membership characterization.                     *)
  intros A f1 f2 a b u v H1 H2 H3. apply Charac3.
  split. 1: assumption. split. 1: assumption. left. split. 2: assumption.
  reflexivity.
Qed.

(* The second branch value belongs to ifThenElse2 when the condition fails.     *)
Proposition Satisfies2 : forall (A:Class) (f1 f2:U -> U -> U) (a b u v:U),
  u :< a -> v :< b -> ~ A :(u,v): ->
  :(:(u,v):,f2 u v): :< ifThenElse2 a b A f1 f2.
Proof.
  (* Proof by Claude.                                                           *)
  (* Follows directly from the membership characterization.                     *)
  intros A f1 f2 a b u v H1 H2 H3. apply Charac3.
  split. 1: assumption. split. 1: assumption. right. split. 2: assumption.
  reflexivity.
Qed.

(* The domain of ifThenElse2 on a x b equals the full product a x b.            *)
Proposition DomainOf : forall (A:Class) (f1 f2:U -> U -> U) (a b:U),
  domain (ifThenElse2 a b A f1 f2) = a :x: b.
Proof.
  (* Proof by Claude.                                                           *)
  (* Every product element appears as a domain element via one of the branches; *)
  (* every domain element is a product element by the membership conditions.    *)
  intros A f1 f2 a b. apply Incl.DoubleInclusion. split; intros x H1.
  - apply Domain.Charac in H1. destruct H1 as [y H1].
    apply Charac2 in H1. destruct H1 as [u [v [H1 [H2 [H3 _]]]]]. subst x.
    apply Prod.Charac. exists u, v. split. 1: reflexivity. split; assumption.
  - apply Prod.Charac in H1. destruct H1 as [u [v [H1 [H2 H3]]]]. subst x.
    apply Domain.Charac.
    assert (A :(u,v): \/ ~ A :(u,v):) as H4. { apply LawExcludedMiddle. }
    destruct H4 as [H4|H4].
    + exists (f1 u v). apply Satisfies1; assumption.
    + exists (f2 u v). apply Satisfies2; assumption.
Qed.

(* ifThenElse2 is a relation: every member is an ordered pair.                  *)
Proposition IsRelation : forall (A:Class) (f1 f2:U -> U -> U) (a b:U),
  Relation (ifThenElse2 a b A f1 f2).
Proof.
  (* Proof by Claude.                                                           *)
  (* Every element has the form of a pair by the membership characterization.   *)
  intros A f1 f2 a b x H1. apply Charac in H1.
  destruct H1 as [u [v [[H1 [H2 [H3 H4]]]|[H1 [H2 [H3 H4]]]]]]; subst.
  - exists :(u,v):. exists (f1 u v). reflexivity.
  - exists :(u,v):. exists (f2 u v). reflexivity.
Qed.

(* ifThenElse2 is functional: the branch condition uniquely determines output.  *)
Proposition IsFunctional : forall (A:Class) (f1 f2:U -> U -> U) (a b:U),
  Functional (ifThenElse2 a b A f1 f2).
Proof.
  (* Proof by Claude.                                                           *)
  (* Two outputs for the same input must come from the same branch, and each    *)
  (* branch yields the same output by the function definitions.                 *)
  intros A f1 f2 a b x y1 y2 H1 H2.
  apply Charac2 in H1. destruct H1 as [u1 [v1 [Hx [H1a [H1b H1c]]]]].
  apply Charac2 in H2. destruct H2 as [u2 [v2 [Hx' [H2a [H2b H2c]]]]].
  rewrite Hx in Hx'. apply OrdPair.WhenEqual in Hx'.
  destruct Hx' as [Hu Hv]. subst u2. subst v2.
  destruct H1c as [[H1c H1d]|[H1c H1d]];
  destruct H2c as [[H2c H2d]|[H2c H2d]];
  try contradiction; subst; reflexivity.
Qed.

(* ifThenElse2 is a function: it is both a relation and functional.             *)
Proposition IsFunction : forall (A:Class) (f1 f2:U -> U -> U) (a b:U),
  Function (ifThenElse2 a b A f1 f2).
Proof.
  (* Proof by Claude.                                                           *)
  intros A f1 f2 a b. split.
  - apply IsRelation.
  - apply IsFunctional.
Qed.

(* ifThenElse2 is a function on the product a x b.                              *)
Proposition IsFunctionOn : forall (A:Class) (f1 f2:U -> U -> U) (a b:U),
  FunctionOn (ifThenElse2 a b A f1 f2) (a :x: b).
Proof.
  (* Proof by Claude.                                                           *)
  intros A f1 f2 a b. split.
  - apply IsFunction.
  - apply DomainOf.
Qed.

(* When the condition holds, evaluating ifThenElse2 returns the first branch.   *)
Proposition Eval1 : forall (A:Class) (f1 f2:U -> U -> U) (a b u v:U),
  u :< a -> v :< b -> A :(u,v): ->
  (ifThenElse2 a b A f1 f2)!(:(u,v):) = f1 u v.
Proof.
  (* Proof by Claude.                                                           *)
  (* The relevant pair belongs to the function; evaluation uniqueness gives     *)
  (* the result.                                                                *)
  intros A f1 f2 a b u v H1 H2 H3.
  apply (FunctionOn.Eval (ifThenElse2 a b A f1 f2) (a :x: b)).
  - apply IsFunctionOn.
  - apply Satisfies1; assumption.
Qed.

(* When the condition fails, evaluating ifThenElse2 returns the second branch.  *)
Proposition Eval2 : forall (A:Class) (f1 f2:U -> U -> U) (a b u v:U),
  u :< a -> v :< b -> ~ A :(u,v): ->
  (ifThenElse2 a b A f1 f2)!(:(u,v):) = f2 u v.
Proof.
  (* Proof by Claude.                                                           *)
  (* The relevant pair belongs to the function; evaluation uniqueness gives     *)
  (* the result.                                                                *)
  intros A f1 f2 a b u v H1 H2 H3.
  apply (FunctionOn.Eval (ifThenElse2 a b A f1 f2) (a :x: b)).
  - apply IsFunctionOn.
  - apply Satisfies2; assumption.
Qed.
