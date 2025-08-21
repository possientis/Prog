Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.UnionGenOfClass.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.UnionGen.

Require Import ZF.Notation.UnionGen.
Export ZF.Notation.UnionGen.

Proposition IsOrdinal : forall (a b:U),
  (forall x, Ordinal b!x) -> Ordinal :\/:_{a} b.
Proof.
  intros a b H1. apply UnionGenOfClass.IsOrdinal. assumption.
Qed.
