Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Induction2.
Require Import ZF.Class.Ordinal.Mult.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Plus.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.UnionGenOfClass.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.Mult.
Export ZF.Notation.Mult.

Module COM := ZF.Class.Ordinal.Mult.
Module SOG := ZF.Set.Ordinal.UnionGenOfClass.


(* The product of two ordinals when a is an ordinal.                            *)
Definition mult (a b:U) : U := (COM.Mult a)!b.

(* Notation "a :*: b" := (mult a b)                                             *)
Global Instance SetMult : Mult U := { mult := mult }.

Proposition WhenZeroR : forall (a:U), a :*: :0: = :0:.
Proof.
  apply COM.WhenZero.
Qed.

Proposition WhenOneR : forall (a:U), Ordinal a ->
  a :*: :1: = a.
Proof.
  intros a H1.
  assert (a :*: :1: = a :*: :0: :+: a) as H2. {
    apply COM.WhenSucc, Core.ZeroIsOrdinal. }
  rewrite H2, WhenZeroR, Plus.WhenZeroL. 2: assumption.
  reflexivity.
Qed.

Proposition WhenSuccR : forall (a b:U), Ordinal b ->
  a :*: (succ b) = a :*: b :+: a.
Proof.
  apply COM.WhenSucc.
Qed.

Proposition WhenLimit : forall (a b:U), Limit b ->
  a :*: b = :\/:_{b} (COM.Mult a).
Proof.
  apply COM.WhenLimit.
Qed.

Proposition IsOrdinal : forall (a b:U), Ordinal a -> Ordinal b ->
  Ordinal (a :*: b).
Proof.
  intros a b H1. revert b. apply Induction2.
  - rewrite WhenZeroR. apply Core.ZeroIsOrdinal.
  - intros b H2 H3. rewrite WhenSuccR. 2: assumption.
    apply Plus.IsOrdinal; assumption.
  - intros b H2 H3. rewrite WhenLimit. 2: assumption.
    apply SOG.IsOrdinal. apply H3.
Qed.

Proposition InOmega : forall (n m:U),
  n :< :N -> m :< :N -> n :*: m :< :N.
Proof.
  intros n m H1. revert m. apply FiniteInduction'.
  - rewrite WhenZeroR. apply Omega.HasZero.
  - intros m H2 H3.
    assert (Ordinal n) as H4. { apply Omega.HasOrdinalElem. assumption. }
    assert (Ordinal m) as H5. { apply Omega.HasOrdinalElem. assumption. }
    assert (Ordinal (n :*: m)) as H6. { apply IsOrdinal; assumption. }
    rewrite WhenSuccR. 2: assumption. apply Plus.InOmega; assumption.
Qed.

