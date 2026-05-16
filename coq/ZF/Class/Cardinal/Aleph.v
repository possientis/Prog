Require Import ZF.Class.Cardinal.InfiniteCard.
Require Import ZF.Class.DiffBySet.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Monotone.
Require Import ZF.Class.Ordinal.Subclass.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageByClass.
Require Import ZF.Set.Relation.RestrictOfClass.

Module CCI := ZF.Class.Cardinal.InfiniteCard.
Module COC := ZF.Class.Ordinal.Core.
Module COM := ZF.Class.Ordinal.Monotone.
Module COS := ZF.Class.Ordinal.Subclass.

(* MinFresh picks the E-minimal element of InfiniteCard not already in range.   *)
Definition MinFresh : Class := COS.MinFresh InfiniteCard.

(* The unique isomorphism between the ordinals and the infinite cardinals.      *)
Definition Aleph : Class := COS.Enum InfiniteCard.

(* Aleph is a function class defined on the ordinals.                           *)
Proposition IsFunctionOn : FunctionOn Aleph Ordinal.
Proof.
  apply COS.IsFunctionOn.
Qed.

(* Aleph is MinFresh-recursive.                                                 *)
Proposition IsRecursive : forall (a:U), Ordinal a ->
  Aleph!a = MinFresh!(Aleph :|: a).
Proof.
  apply COS.IsRecursive.
Qed.

(* Aleph(a) is the least infinite cardinal not in the image aleph[a].           *)
Proposition IsMinimal : forall (a:U), Ordinal a ->
  Minimal E (InfiniteCard :\: Aleph:[a]:) Aleph!a.
Proof.
  intros a H1.
  apply COS.IsMinimal. 3: assumption.
  - apply CCI.IsProper.
  - intros b. apply CCI.IsOrdinal.
Qed.

Proposition IsInf : forall (a:U), Ordinal a ->
  Aleph!a = inf (InfiniteCard :\: Aleph:[a]:).
Proof.
  intros a H1. apply COS.IsInf. 3: assumption.
  - apply CCI.IsProper.
  - intros b. apply CCI.IsOrdinal.
Qed.

(* Aleph is an isomorphism between the ordinals and infinite cardinals.         *)
Proposition IsIsom : Isom Aleph E E Ordinal InfiniteCard.
Proof.
  apply COS.IsIsom.
  - apply CCI.IsProper.
  - intros a. apply CCI.IsOrdinal.
Qed.

(* Aleph is the unique isomorphism ...                                          *)
Proposition IsUnique : forall (F:Class),
  Isom F E E Ordinal InfiniteCard -> F :~: Aleph.
Proof.
  intros F. apply COS.IsUnique.
  - apply CCI.IsProper.
  - intros a. apply CCI.IsOrdinal.
Qed.

(* Aleph is strictly monotone.                                                  *)
Proposition IsMonotone : Monotone Aleph.
Proof.
  apply COS.IsMonotone.
  - apply CCI.IsProper.
  - intros a. apply CCI.IsOrdinal.
Qed.

(* The domain of Aleph is the class of ordinals.                                *)
Proposition DomainOf : domain Aleph :~: Ordinal.
Proof.
  apply IsIsom.
Qed.

(* Aleph(a) is no less than a.                                                  *)
Proposition IsIncl : forall (a:U), Ordinal a ->
  a :<=: Aleph!a.
Proof.
  intros a H1. apply COM.IsIncl.
  - apply IsMonotone.
  - apply DomainOf. assumption.
Qed.

