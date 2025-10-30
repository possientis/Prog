Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Plus.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.Plus.
Export ZF.Notation.Plus.

Module COP := ZF.Class.Ordinal.Plus.

(* The sum of two ordinals when a is an ordinal.                                *)
Definition plus (a b:U) : U := (COP.Plus a)!b.

(* Notation "a :+: b" := ((plus a)!b)                                           *)
Global Instance SetPlus : Plus U := { plus := plus }.

Proposition WhenZero : forall (a:U), a :+: :0: = a.
Proof.
  apply COP.WhenZero.
Qed.

Proposition WhenOne : forall (a:U), a :+: :1: = succ a.
Proof.
  intros a.
  assert (a :+: :1: = succ (a :+: :0:)) as H1. {
    apply COP.WhenSucc, Natural.ZeroIsOrdinal. }
  rewrite H1. rewrite WhenZero. reflexivity.
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

