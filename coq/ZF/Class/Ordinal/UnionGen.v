Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Union.
Require Import ZF.Class.UnionGen.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.

Require Import ZF.Notation.UnionGen.
Export ZF.Notation.UnionGen.

Proposition IsOrdinal : forall (A B:Class),
  (forall x, On (B!x)) -> Ordinal :\/:_{A} B.
Proof.
  intros A B H1. apply Union.IsOrdinal. intros y H2.
  destruct H2 as [x [H2 H3]]. subst. apply H1.
Qed.
