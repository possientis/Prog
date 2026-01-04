Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.OrdFun.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Range.

Definition OrdFunOn (f a:U) : Prop :=
  Function f                              /\
  domain f = a                            /\
  Ordinal a                               /\
  (forall y, y :< range f -> Ordinal y).

Definition Decreasing (f:U) : Prop := forall (x y:U),
  x   :< domain f ->
  y   :< domain f ->
  x   :< y        ->
  f!y :< f!x.

Proposition IsOrdFun : forall (f a:U), OrdFunOn f a ->
  OrdFun f.
Proof.
  intros f a [H1 [H2 [H3 H4]]].
  split. 1: assumption. split. 2: assumption. subst. assumption.
Qed.

Proposition IsOrdinal : forall (f a x:U), OrdFunOn f a ->
  x :< a -> Ordinal f!x.
Proof.
  intros f a x H1 H2. apply OrdFun.IsOrdinal.
  - apply IsOrdFun with a. assumption.
  - destruct H1 as [H1 [H3 _]]. subst. assumption.
Qed.

