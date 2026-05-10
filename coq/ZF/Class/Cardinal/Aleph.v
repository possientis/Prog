Require Import ZF.Class.Cardinal.InfiniteCard.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Monotone.
Require Import ZF.Class.Ordinal.OrdSub.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Relation.EvalOfClass.

Module CCI := ZF.Class.Cardinal.InfiniteCard.
Module CEQ := ZF.Class.Equiv.
Module COC := ZF.Class.Ordinal.Core.
Module COM := ZF.Class.Ordinal.Monotone.
Module COO := ZF.Class.Ordinal.OrdSub.

(* The unique isomorphism between the ordinals and the infinite cardinals.      *)
Definition Aleph : Class := COO.Enum InfiniteCard.

(* Aleph is an isomorphism between the ordinals and infinite cardinals.         *)
Proposition IsIsom : Isom Aleph E E Ordinal InfiniteCard.
Proof.
  apply COO.IsIsom.
  - apply CCI.IsProper.
  - intros a. apply CCI.IsOrdinal.
  - apply CEQ.Refl.
Qed.

(* Aleph is the unique isomorphism ...                                          *)
Proposition IsUnique : forall (F:Class),
  Isom F E E Ordinal InfiniteCard -> F :~: Aleph.
Proof.
  intros F. apply COO.IsUnique.
  - apply CCI.IsProper.
  - intros a. apply CCI.IsOrdinal.
Qed.

Proposition IsMonotone : Monotone Aleph.
Proof.
  apply COM.FromIsom with Ordinal InfiniteCard.
  - apply IsIsom.
  - apply COC.IsOrdinal.
  - intros a. apply CCI.IsOrdinal.
Qed.

Proposition DomainOf : domain Aleph :~: Ordinal.
Proof.
  apply IsIsom.
Qed.

Proposition IsIncl : forall (a:U), Ordinal a ->
  a :<=: Aleph!a.
Proof.
  intros a H1. apply COM.IsIncl.
  - apply IsMonotone.
  - apply DomainOf. assumption.
Qed.

