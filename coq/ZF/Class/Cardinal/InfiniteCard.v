Require Import ZF.Class.Cardinal.Core.
Require Import ZF.Class.DiffBySet.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Proper.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Omega.

Module CCC := ZF.Class.Cardinal.Core.
Module SCC := ZF.Set.Cardinal.Core.
Module SOC := ZF.Set.Ordinal.Core.
Module SOI := ZF.Set.Ordinal.InfOfClass.

(* The class of infinite cardinal numbers.                                      *)
Definition InfiniteCard : Class := Cardinal :\: :N.

(* The class of infinite cardinal numbers is a proper class.                    *)
Proposition IsProper : Proper InfiniteCard.
Proof.
  apply DiffBySet.IsProper, CCC.IsProper.
Qed.

Proposition IsCardinal : forall (a:U),
  InfiniteCard a -> Cardinal a.
Proof.
  apply DiffBySet.IsInclL.
Qed.

Proposition IsOrdinal : forall (a:U),
  InfiniteCard a -> Ordinal a.
Proof.
  intros a H1. apply SCC.CardIsOrd, IsCardinal. assumption.
Qed.

(* omega is a cardinal number not contained in itself.                          *)
Proposition HasOmega : InfiniteCard :N.
Proof.
  (* Proof by Claude.                                                           *)
  (* N is a cardinal number not a member of itself by foundation.               *)
  split.
  - apply SCC.HasOmega.
  - apply Foundation.NoLoop1.
Qed.

(* Every infinite cardinal contains omega as a subset.                          *)
Proposition IsIncl : forall (a:U), InfiniteCard a -> :N :<=: a.
Proof.
  (* Proof by Claude.                                                           *)
  (* An infinite cardinal a is an ordinal not in omega. Since ordinals are      *)
  (* totally ordered by membership, either a is in omega or omega is included   *)
  (* in a. The first is ruled out, so omega is a subset of a.                   *)
  intros a H1.
  assert (a :< :N \/ :N :<=: a) as H2. {
    apply SOC.ElemOrIncl.
    - apply IsOrdinal. assumption.
    - apply Omega.IsOrdinal. }
  destruct H2 as [H2|H2]. 2: assumption. exfalso.
  apply DiffBySet.Charac in H1. destruct H1 as [_ H3].
  apply H3. assumption.
Qed.

(* The infimum of the class of infinite cardinals is omega.                     *)
Proposition Inf : inf InfiniteCard = :N.
Proof.
  (* Proof by Claude.                                                           *)
  (* We prove double inclusion. Omega is an infinite cardinal, so the infimum   *)
  (* is at most omega. Every infinite cardinal contains omega, so omega is a    *)
  (* lower bound, and the infimum is at least omega.                            *)
  apply Incl.Double. split.
  - (* The infimum is at most omega, since omega is an infinite cardinal.       *)
    apply SOI.IsLowerBound.
    + intros a H1. apply IsOrdinal. assumption.
    + apply HasOmega.
  - (* The infimum is at least omega: omega is a lower bound of the class.      *)
    apply SOI.IsLargest.
    + intros a H1. apply IsOrdinal. assumption.
    + (* The class of infinite cardinals is non-empty, as it contains omega.    *)
      apply Class.Empty.HasElem. exists :N. apply HasOmega.
    + (* Every infinite cardinal contains omega.                                *)
      intros a H1. apply IsIncl. assumption.
Qed.
