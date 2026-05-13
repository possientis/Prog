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

(* The union of a class family of ordinals indexed by a is an ordinal.          *)
Proposition IsOrdinal : forall (A:Class) (a:U),
  (forall x, x :< a -> Ordinal A!x) -> Ordinal :\/:_{a} A.
Proof.
  intros A a H1. unfold Ordinal, On. apply COC.EquivCompat with :\/:_{toClass a} A.
  - apply Equiv.Sym, FromClass.ToClass.
  - apply UnionGen.IsOrdinal. assumption.
Qed.

(* The union of the identity family over a limit ordinal equals that ordinal.   *)
Proposition WhenLimit : forall (a:U), Limit a -> :\/:_{a} I = a.
Proof.
  intros a H1. apply Incl.Double. split; intros b H2.
  - apply SUC.Charac in H2. destruct H2 as [c [H2 H3]].
    rewrite I.Eval in H3.
    assert (Ordinal a) as G1. { apply H1. }
    assert (Transitive a) as G2. { apply Core.Charac in G1. apply G1. }
    apply G2 with c; assumption.
  - apply SUC.Charac.
    assert (exists c, b :< c /\ c :< a) as H3. {
      apply Limit.InBetween; assumption. }
    destruct H3 as [c [H3 H4]]. exists c. split. 1: assumption.
    rewrite I.Eval. assumption.
Qed.

