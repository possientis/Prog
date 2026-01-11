Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.OrdFun.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Range.

Definition OrdFunOn (f a:U) : Prop := OrdFun f /\ domain f = a.

Proposition IsOrdinal : forall (f a x:U), OrdFunOn f a ->
  x :< a -> Ordinal f!x.
Proof.
  intros f a x H1 H2.
  apply OrdFun.IsOrdinal.
  - apply H1.
  - assert (domain f = a) as H3. { apply H1. }
    subst. assumption.
Qed.

Proposition DomainOf : forall (f a:U), OrdFunOn f a -> Ordinal a.
Proof.
  intros f a [[H1 [H2 H3]] H4]. subst. assumption.
Qed.

