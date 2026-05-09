Require Import ZF.Class.Cardinal.Core.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Ordinal.OrdSub.
Require Import ZF.Class.Proper.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Omega.

Module CCC := ZF.Class.Cardinal.Core.
Module CEQ := ZF.Class.Equiv.
Module CIN := ZF.Class.Incl.
Module COO := ZF.Class.Ordinal.OrdSub.
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

(* The unique isomorphism between the ordinals and the infinite cardinals.      *)
Definition Aleph : Class := COO.RecurseSmallestFresh InfiniteCard.

(* Aleph is an isomorphism between the ordinals and infinite cardinals.         *)
Proposition IsIsom : Isom Aleph E E Ordinal InfiniteCard.
Proof.
  apply COO.IsIsom.
  - apply IsProper.
  - intros a. apply IsOrdinal.
  - apply CEQ.Refl.
Qed.

(* Aleph is the unique isomorphism ...                                          *)
Proposition IsUnique : forall (F:Class),
  Isom F E E Ordinal InfiniteCard -> F :~: Aleph.
Proof.
  intros F. apply COO.IsUnique.
  - apply IsProper.
  - intros a. apply IsOrdinal.
Qed.

