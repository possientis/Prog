Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.


(* The class of non-limit ordinals.                                             *)
Definition NonLimit : Class := fun a =>
  a = :0: \/ exists b, Ordinal b /\ a = succ b.

(* NonLimit is a class of ordinals.                                             *)
Proposition IsClassOfOrdinals : NonLimit :<=: On.
Proof.
  intros a [H1|H1].
  - subst. apply ZeroIsOrdinal.
  - destruct H1 as [b [H1 H2]]. rewrite H2. apply Succ.IsOrdinal. assumption.
Qed.

Proposition HasSucc : forall (a:U), Ordinal a ->
  NonLimit (succ a).
Proof.
  intros a H1. right. exists a. split.
  - assumption.
  - reflexivity.
Qed.
