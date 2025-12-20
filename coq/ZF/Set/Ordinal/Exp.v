Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Exp.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Mult.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.UnionOf.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Union.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.Exp.
Export ZF.Notation.Exp.

Module COE := ZF.Class.Ordinal.Exp.

(* The exponentiation of two ordinals when a is an ordinal.                     *)
Definition exp (a b:U) : U := (COE.Exp a)!b.

(* Notation "a :^: b" := (exp a b)                                              *)
Global Instance SetExp : Exp U := { exp := exp }.

Proposition WhenZeroR : forall (a:U), a :^: :0: = :1:.
Proof.
  intros a. apply COE.WhenZero.
Qed.

Proposition WhenSuccR : forall (a b:U), Ordinal b ->
  a :^: (succ b) = a :^: b :*: a.
Proof.
  apply COE.WhenSucc.
Qed.

Proposition WhenLimit : forall (a b:U), Limit b ->
  :0: :< a  -> a :^: b = :\/:_{b} (COE.Exp a).
Proof.
  intros a b H1 H2.
  apply COE.WhenLimit. 1: assumption. apply Empty.HasElem.
  exists :0:. assumption.
Qed.

Proposition WhenLimitZero : forall (a b:U), Limit b ->
  a = :0: -> a :^: b  = :0:.
Proof.
  apply COE.WhenLimitZero.
Qed.

Proposition WhenZeroL : forall (a:U), Ordinal a ->
  :0: :< a -> :0: :^: a = :0:.
Proof.
  intros a H1 H2.
  assert (a = succ :U(a) \/ Limit a) as H3. { apply Limit.TwoWay; assumption. }
  destruct H3 as [H3|H3].
  - rewrite H3, WhenSuccR, Mult.WhenZeroR. 1: reflexivity.
    apply UnionOf.IsOrdinal. assumption.
  - rewrite WhenLimitZero; try reflexivity. assumption.
Qed.

