Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.UnionGen.
Require Import ZF.Class.Relation.I.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Transitive.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.UnionGen.
Export ZF.Notation.UnionGen.

Module COC := ZF.Class.Ordinal.Core.
Module SUC := ZF.Set.UnionGenOfClass.

Proposition IsOrdinal : forall (A:Class) (a:U),
  (forall x, x :< a -> Ordinal A!x) -> Ordinal :\/:_{a} A.
Proof.
  intros A a H1. unfold Ordinal, On. apply COC.EquivCompat with :\/:_{toClass a} A.
  - apply Equiv.Sym, FromClass.ToFromClass.
  - apply UnionGen.IsOrdinal. assumption.
Qed.

Proposition WhenLimit : forall (a:U), Limit a -> :\/:_{a} I = a.
Proof.
  intros a H1. apply DoubleInclusion. split; intros b H2.
  - apply SUC.Charac in H2. destruct H2 as [c [H2 H3]].
    rewrite I.Eval in H3. apply Transitive.WhenOrdinal with c; try assumption.
    apply H1.
  - apply SUC.Charac.
    assert (exists c, b :< c /\ c :< a) as H3. {
      apply Limit.InBetween; assumption. }
    destruct H3 as [c [H3 H4]]. exists c. split. 1: assumption.
    rewrite I.Eval. assumption.
Qed.

