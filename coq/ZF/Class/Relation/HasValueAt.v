Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.FunctionalAt.
Require Export ZF.Class.Relation.IsValueAt.
Require Import ZF.Class.Inter2.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that the class F has a value at a.             *)
Definition HasValueAt (F:Class) (a:U) : Prop := exists y, IsValueAt F a y.

Proposition AsInter : forall (F:Class),
  HasValueAt F :~: FunctionalAt F :/\: domain F.
Proof.
  intros F a. split; intros H1.
  - destruct H1 as [y [H1 H2]]. split. 1: assumption.
    exists y. assumption.
  - destruct H1 as [H1 H2]. destruct H2 as [y H2]. exists y.
    apply IsValueAt.WhenFunctionalAt; assumption.
Qed.

Proposition WhenFunctionalAt : forall (F:Class) (a:U),
  FunctionalAt F a -> HasValueAt F a <-> domain F a.
Proof.
  intros F a H1. split; intros H2.
  - apply AsInter in H2. apply H2.
  - apply AsInter. split; assumption.
Qed.

(* When F is functional, the classes HasValueAt F and domain F coincide.        *)
Proposition WhenFunctional : forall (F:Class),
  Functional F -> HasValueAt F :~: domain F.
Proof.
  intros F H1 a.
  apply WhenFunctionalAt, IsFunctionalAt. assumption.
Qed.
