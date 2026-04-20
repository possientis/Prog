Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Fun.IfThenElse.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Relation.RestrictOfClass.

Require Import ZF.Notation.Eval.

Module CFI := ZF.Class.Relation.Fun.IfThenElse.
Module SOR := ZF.Set.Relation.RestrictOfClass.

(* The function defined on the set a by:                                        *)
(* f(x) = f1(x) if A x                                                          *)
(* f(x) = f2(x) if ~ A X                                                        *)
Definition ifThenElse (a:U)(A:Class)(f1 f2:U -> U) : U
  := (CFI.ifThenElse A f1 f2) :|: a.

Proposition Charac : forall (A:Class) (f1 f2:U -> U) (a x:U),
  x :< ifThenElse a A f1 f2 <-> exists y,
    x = :(y,f1 y): /\ y :< a /\ A y \/ x = :(y,f2 y): /\ y :< a /\ ~ A y.
Proof.
  intros A f1 f2 a x. split; intros H1.
  - apply SOR.Charac in H1. 2: apply CFI.IsFunctional.
    destruct H1 as [y [z [H1 [H2 H3]]]].
    apply CFI.Charac2 in H3. destruct H3 as [[H3 H4]|[H3 H4]]; subst; exists y.
    + left.  split. 1: reflexivity. split; assumption.
    + right. split. 1: reflexivity. split; assumption.
  - destruct H1 as [y [[H1 [H2 H3]]|[H1 [H2 H3]]]]; subst.
    + apply SOR.Charac2Rev. 2: assumption.
      * apply CFI.IsFunctional.
      * apply CFI.Satisfies1. assumption.
    + apply SOR.Charac2Rev. 2: assumption.
      * apply CFI.IsFunctional.
      * apply CFI.Satisfies2. assumption.
Qed.

Proposition Charac2 : forall (A:Class) (f1 f2:U -> U) (a x y:U),
  :(x,y): :< ifThenElse a A f1 f2     <->
    y = f1 x /\ x :< a /\ A x      \/
    y = f2 x /\ x :< a /\ ~ A x.
Proof.
  intros A f1 f2 a x y. split; intros H1.
  - apply Charac in H1. destruct H1 as [z [[H1 [H2 H3]]|[H1 [H2 H3]]]];
    apply OrdPair.WhenEqual in H1; destruct H1 as [H1 H4]; subst.
    + left.  split. 1: reflexivity. split; assumption.
    + right. split. 1: reflexivity. split; assumption.
  - destruct H1 as [[H1 [H2 H3]]|[H1 [H2 H3]]]; subst; apply Charac; exists x.
    + left. split. 1: reflexivity. split; assumption.
    + right. split. 1: reflexivity. split; assumption.
Qed.

Proposition Satisfies1 : forall (A:Class) (f1 f2:U -> U) (a x:U),
  x :< a -> A x -> :(x,f1 x): :< ifThenElse a A f1 f2.
Proof.
  intros A f1 f2 a x H1 H2. apply Charac2. left.
  split. 1: reflexivity. split; assumption.
Qed.

Proposition Satisfies2 : forall (A:Class) (f1 f2:U -> U) (a x:U),
  x :< a -> ~ A x -> :(x,f2 x): :< ifThenElse a A f1 f2.
Proof.
  intros A f1 f2 a x H1 H2. apply Charac2. right.
  split. 1: reflexivity. split; assumption.
Qed.

Proposition DomainOf : forall (A:Class) (f1 f2:U -> U) (a:U),
  domain (ifThenElse a A f1 f2) = a.
Proof.
  intros A f1 f2 a. apply Incl.DoubleInclusion. split; intros x H1.
  - apply Domain.Charac in H1. destruct H1 as [y H1].
    apply Charac2 in H1. destruct H1 as [H1|H1]; apply H1.
  - apply Domain.Charac.
    assert (A x \/ ~ A x) as H2. { apply LawExcludedMiddle. }
    destruct H2 as [H2|H2].
    + exists (f1 x). apply Satisfies1; assumption.
    + exists (f2 x). apply Satisfies2; assumption.
Qed.

Proposition IsRelation : forall (A:Class) (f1 f2:U -> U) (a:U),
  Relation (ifThenElse a A f1 f2).
Proof.
  intros A f1 f2 a x H1. apply Charac in H1.
  destruct H1 as [y [[H1 [H2 H3]]|[H1 [H2 H3]]]]; exists y.
  - exists (f1 y). assumption.
  - exists (f2 y). assumption.
Qed.

Proposition IsFunctional : forall (A:Class) (f1 f2:U -> U) (a:U),
  Functional (ifThenElse a A f1 f2).
Proof.
  intros A f1 f2 a x y1 y2 H1 H2.
  apply Charac2 in H1. apply Charac2 in H2.
  destruct H1 as [[H1 [H3 H4]]|[H1 [H3 H4]]];
  destruct H2 as [[H2 [H5 H6]]|[H2 [H5 H6]]];
  try contradiction; subst; reflexivity.
Qed.

Proposition IsFunction : forall (A:Class) (f1 f2:U -> U) (a:U),
  Function (ifThenElse a A f1 f2).
Proof.
  intros A f1 f2 a. split.
  - apply IsRelation.
  - apply IsFunctional.
Qed.

Proposition IsFunctionOn : forall (A:Class) (f1 f2:U -> U) (a:U),
  FunctionOn (ifThenElse a A f1 f2) a.
Proof.
  intros A f1 f2 a. split.
  - apply IsFunction.
  - apply DomainOf.
Qed.

Proposition Eval1 : forall (A:Class) (f1 f2:U -> U) (a x:U),
  x :< a -> A x -> (ifThenElse a A f1 f2)!x = f1 x.
Proof.
  intros A f1 f2 a x H1 H2. apply Eval.Charac.
  - apply IsFunctional.
  - rewrite DomainOf. assumption.
  - apply Satisfies1; assumption.
Qed.

Proposition Eval2 : forall (A:Class) (f1 f2:U -> U) (a x:U),
  x :< a -> ~ A x -> (ifThenElse a A f1 f2)!x = f2 x.
Proof.
  intros A f1 f2 a x H1 H2. apply Eval.Charac.
  - apply IsFunctional.
  - rewrite DomainOf. assumption.
  - apply Satisfies2; assumption.
Qed.
