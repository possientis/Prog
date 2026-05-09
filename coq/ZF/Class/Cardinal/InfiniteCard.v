Require Import ZF.Class.Cardinal.Core.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Proper.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Omega.

Module CCC := ZF.Class.Cardinal.Core.
Module SCC := ZF.Set.Cardinal.Core.

(* The class of infinite cardinal numbers.                                      *)
Definition InfiniteCard : Class := Cardinal :\: toClass :N.

(* The class of infinite cardinal numbers is a proper class.                    *)
Proposition IsProper : Proper InfiniteCard.
Proof.
  apply Diff.MinusASet, CCC.IsProper.
Qed.

Proposition IsCardinal : forall (a:U),
  InfiniteCard a -> Cardinal a.
Proof.
  apply Diff.IsInclL.
Qed.

Proposition IsOrdinal : forall (a:U),
  InfiniteCard a -> Ordinal a.
Proof.
  intros a H1. apply SCC.CardIsOrd, IsCardinal. assumption.
Qed.


