Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.UnionGen.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.UnionGen.
Export ZF.Notation.UnionGen.

Module COC := ZF.Class.Ordinal.Core.

Proposition IsOrdinal : forall (A:Class) (a:U),
  (forall x, Ordinal A!x) -> Ordinal :\/:_{a} A.
Proof.
  intros A a H1. unfold Ordinal, On. apply COC.EquivCompat with :\/:_{toClass a} A.
  - apply Equiv.Sym, FromClass.ToFromClass.
  - apply UnionGen.IsOrdinal. assumption.
Qed.

