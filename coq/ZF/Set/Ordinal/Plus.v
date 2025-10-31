Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Induction2.
Require Import ZF.Class.Ordinal.Plus.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.UnionGenOfClass.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.Plus.
Export ZF.Notation.Plus.

Module COP := ZF.Class.Ordinal.Plus.
Module SOU := ZF.Set.Ordinal.UnionGenOfClass.
Module SUC := ZF.Set.UnionGenOfClass.

(* The sum of two ordinals when a is an ordinal.                                *)
Definition plus (a b:U) : U := (COP.Plus a)!b.

(* Notation "a :+: b" := ((plus a)!b)                                           *)
Global Instance SetPlus : Plus U := { plus := plus }.

Proposition WhenZeroR : forall (a:U), a :+: :0: = a.
Proof.
  apply COP.WhenZero.
Qed.

Proposition WhenOneR : forall (a:U), a :+: :1: = succ a.
Proof.
  intros a.
  assert (a :+: :1: = succ (a :+: :0:)) as H1. {
    apply COP.WhenSucc, Natural.ZeroIsOrdinal. }
  rewrite H1. rewrite WhenZeroR. reflexivity.
Qed.

Proposition WhenSucc : forall (a b:U), Ordinal b ->
  a :+: (succ b) = succ (a :+: b).
Proof.
  apply COP.WhenSucc.
Qed.

Proposition WhenLimit : forall (a b:U), Limit b ->
  a :+: b = :\/:_{b} (COP.Plus a).
Proof.
  apply COP.WhenLimit.
Qed.

Proposition IsOrdinal : forall (a b:U), Ordinal a -> Ordinal b ->
  Ordinal (a :+: b).
Proof.
  intros a b H1. revert b. apply Induction2.
  - rewrite WhenZeroR. assumption.
  - intros b H2 H3. rewrite WhenSucc. 2: assumption.
    apply Succ.IsOrdinal. assumption.
  - intros b H2 H3. rewrite WhenLimit. 2: assumption.
    apply SOU.IsOrdinal. intros c H4. apply H3. assumption.
Qed.

Proposition WhenZeroL : forall (a:U), Ordinal a ->
  :0: :+: a = a.
Proof.
  apply Induction2.
  - apply WhenZeroR.
  - intros a H1 H2. rewrite WhenSucc. 2: assumption. rewrite H2. reflexivity.
  - intros a H1 H2. rewrite WhenLimit. 2: assumption.
    rewrite <- SOU.WhenLimit. 2: assumption.
    apply SUC.EqualCharac. intros x. rewrite I.Eval. apply H2.
Qed.
