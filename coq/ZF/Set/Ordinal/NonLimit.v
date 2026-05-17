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

(* Every non-limit ordinal is an ordinal.                                       *)
Proposition HasOrdinals : NonLimit :<=: Ordinal.
Proof.
  intros a [H1|H1].
  - subst. apply Core.Zero.
  - destruct H1 as [b [H1 H2]]. subst. apply Succ.IsOrdinal. assumption.
Qed.

(* An ordinal is non-limit iff it is 0 or the successor of its own union.       *)
Proposition Charac : forall (a:U), Ordinal a ->
  NonLimit a <-> a = :0: \/ a = succ :U(a).
Proof.
  intros a H1. split; intros H2.
  - destruct H2 as [H2|H2].
    + left. assumption.
    + right. apply Succ.OfUnion in H2. 2: assumption. symmetry. assumption.
  - destruct H2 as [H2|H2].
    + left. assumption.
    + right. symmetry in H2. apply Succ.OfUnion in H2; assumption.
Qed.

(* A successor ordinal is a non-limit ordinal.                                  *)
Proposition HasSucc : forall (a:U), Ordinal a ->
  NonLimit (succ a).
Proof.
  intros a H1. right. exists a. split. 1: assumption. reflexivity.
Qed.
