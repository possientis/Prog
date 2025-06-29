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
  a = :0: \/ exists b, Ordinal b /\ a = succ b.

(* NonLimit is a class of ordinals.                                             *)
Proposition HasOrdinalElem : NonLimit :<=: Ordinal.
Proof.
  intros a [H1|H1].
  - subst. apply ZeroIsOrdinal.
  - destruct H1 as [b [H1 H2]]. rewrite H2. apply Succ.IsOrdinal. assumption.
Qed.

Proposition Charac : forall (a:U), Ordinal a ->
  NonLimit a <-> a = :0: \/ a = succ :U(a).
Proof.
  intros a H1. split; intros H2.
  - destruct H2 as [H2|H2].
    + left. assumption.
    + destruct H2 as [b [H2 H3]]. right.
      assert (:U(a) = b) as H4. { rewrite H3. apply UnionOfSucc. assumption. }
      rewrite H4. assumption.
  - destruct H2 as [H2|H2].
    + left. assumption.
    + right. exists :U(a). split. 2: assumption. apply Union.IsOrdinal.
      apply Core.IsLess. assumption.
Qed.

(* A successor ordinal is a non-limit ordinal.                                  *)
Proposition HasSucc : forall (a:U), Ordinal a ->
  NonLimit (succ a).
Proof.
  intros a H1. right. exists a. split.
  - assumption.
  - reflexivity.
Qed.

