Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Inter.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Inf.
Require Import ZF.Set.Specify.

(* The infimum of an ordinal is simply its intersection.                        *)
Proposition IsInter : forall (a:U), Ordinal a ->
  inf a = :I(a).
Proof.
  intros a H1. unfold inf.
  assert (:{ x:< a | Ordinal }: = a) as H2. {
    apply Specify.IsA. intros x H2. apply Core.IsOrdinal with a; assumption. }
  rewrite H2. reflexivity.
Qed.

Proposition IsZero : forall (a:U), Ordinal a ->
  inf a = :0:.
Proof.
  intros a H1. rewrite IsInter. 2: assumption.
  apply Inter.IsZero. assumption.
Qed.
