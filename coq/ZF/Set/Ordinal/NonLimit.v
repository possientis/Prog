Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.SuccOf.
Require Import ZF.Set.Ordinal.Union.
Require Import ZF.Set.Union.


(* The class of non-limit ordinals.                                             *)
Definition NonLimit : Class := fun a =>
  a = :0: \/ Successor a.

(* NonLimit is a class of ordinals.                                             *)
Proposition HasOrdinalElem : NonLimit :<=: Ordinal.
Proof.
  intros a [H1|H1].
  - subst. apply Core.ZeroIsOrdinal.
  - apply H1.
Qed.

Proposition Charac : forall (a:U), Ordinal a ->
  NonLimit a <-> a = :0: \/ a = succ :U(a).
Proof.
  intros a H1. split; intros H2.
  - destruct H2 as [H2|H2].
    + left. assumption.
    + right. apply Succ.WhenSuccessor in H2; assumption.
  - destruct H2 as [H2|H2].
    + left. assumption.
    + right. apply Succ.WhenSuccessor in H2; assumption.
Qed.

(* A successor ordinal is a non-limit ordinal.                                  *)
Proposition HasSucc : forall (a:U), Ordinal a ->
  NonLimit (succ a).
Proof.
  intros a H1. right. split.
  - apply Succ.IsOrdinal. assumption.
  - exists a. reflexivity.
Qed.
