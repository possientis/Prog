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

(* Given Coq expressions f1 and f2 representing functions on sets and a class A *)
(* we aim to quickly define the function class F such that:                     *)
(* F(x) = f1(x) if A x                                                          *)
(* F(x) = f2(x) if ~ A x                                                        *)
Definition toFun2 (A:Class) (f1 f2:U -> U) : Class := fun x => exists y,
  x = :(y, f1 y): /\   A y    \/
  x = :(y, f2 y): /\ ~ A y.

Proposition Charac2 : forall (A:Class) (f1 f2:U -> U) (x y:U),
  toFun2 A f1 f2 :(x,y): <-> y = f1 x /\ A x \/ y = f2 x /\ ~ A x.
Proof.
  intros A f1 f2 x y. split; intros H1.
  - destruct H1 as [z [[H1 H2]|[H1 H2]]];
    apply OrdPair.WhenEqual in H1; destruct H1 as [H1 H3]; subst.
    + left. split. 2: assumption. reflexivity.
    + right. split. 2: assumption. reflexivity.
  - destruct H1 as [[H1 H2]|[H1 H2]]; exists x; subst.
    + left. split. 2: assumption. reflexivity.
    + right. split. 2: assumption. reflexivity.
Qed.

Proposition Satisfies1 : forall (A:Class) (f1 f2:U -> U) (a:U),
  A a -> toFun2 A f1 f2 :(a, f1 a):.
Proof.
  intros A f1 f2 a H1. apply Charac2. left. split. 2: assumption. reflexivity.
Qed.

Proposition Satisfies2 : forall (A:Class) (f1 f2:U -> U) (a:U),
  ~ A a -> toFun2 A f1 f2 :(a, f2 a):.
Proof.
  intros A f1 f2 a H1. apply Charac2. right. split. 2: assumption. reflexivity.
Qed.

Proposition DomainOf : forall (A:Class) (f1 f2:U -> U) (a:U),
  domain (toFun2 A f1 f2) a.
Proof.
  intros A f1 f2 a.
  assert (A a \/ ~ A a) as H1. { apply LawExcludedMiddle. }
  destruct H1 as [H1|H1].
  - exists (f1 a). apply Satisfies1. assumption.
  - exists (f2 a). apply Satisfies2. assumption.
Qed.

Proposition IsRelation : forall (A:Class) (f1 f2:U -> U),
  Relation (toFun2 A f1 f2).
Proof.
  intros A f1 f2 x H1. destruct H1 as [y [[H1 H2]|[H1 H2]]]; exists y.
  - exists (f1 y). assumption.
  - exists (f2 y). assumption.
Qed.

Proposition IsFunctional : forall (A:Class) (f1 f2:U -> U),
  Functional (toFun2 A f1 f2).
Proof.
  intros A f1 f2 x y1 y2 H1 H2.
  apply Charac2 in H1. apply Charac2 in H2.
  destruct H1 as [[H1 H3]|[H1 H3]]; destruct H2 as [[H2 H4]|[H2 H4]];
  try contradiction; subst; reflexivity.
Qed.

Proposition IsFunction : forall (A:Class) (f1 f2:U -> U),
  Function (toFun2 A f1 f2).
Proof.
  intros A f1 f2. split.
  - apply IsRelation.
  - apply IsFunctional.
Qed.

Proposition Eval1 : forall (A:Class) (f1 f2:U -> U) (a:U),
  A a -> (toFun2 A f1 f2)!a = f1 a.
Proof.
  intros A f1 f2 a H1. apply EvalOfClass.Charac.
  - apply IsFunctional.
  - apply DomainOf.
  - apply Satisfies1. assumption.
Qed.

Proposition Eval2 : forall (A:Class) (f1 f2:U -> U) (a:U),
  ~ A a -> (toFun2 A f1 f2)!a = f2 a.
Proof.
  intros A f1 f2 a H1. apply EvalOfClass.Charac.
  - apply IsFunctional.
  - apply DomainOf.
  - apply Satisfies2. assumption.
Qed.


