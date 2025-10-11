Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Founded.
Require Import ZF.Class.Order.Irreflexive.
Require Import ZF.Class.Order.StrictOrd.
Require Import ZF.Class.Order.StrictTotalOrd.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.Transitive.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Class.Order.WellOrdering.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.V.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.OrdPair.

Module COC := ZF.Class.Ordinal.Core.
Module SOC := ZF.Set.Ordinal.Core.

(* The order :< is irreflexive on any class A.                                  *)
Proposition IsIrreflexive : forall (A:Class),
  Irreflexive E A.
Proof.
  intros A x H1 H2. apply E.Charac2 in H2. revert H2. apply NoElemLoop1.
Qed.

(* The order :< is transitive on any class of ordinals.                         *)
Proposition IsTransitive : forall (A:Class),
  A :<=: On -> Transitive E A.
Proof.
  intros A H1 x y z H2 H3 H4 H5 H6.
  apply E.Charac2 in H5. apply E.Charac2 in H6. apply E.Charac2.
  apply SOC.ElemElemTran with y; try assumption; apply H1; assumption.
Qed.

(* The order :< is total on any class of ordinals.                              *)
Proposition IsTotal : forall (A:Class),
  A :<=: On -> Total E A.
Proof.
  intros A H1 x y H2 H3.
  assert (x = y \/ x :< y \/ y :< x) as H4. {
    apply SOC.IsTotal; apply H1; assumption. }
  destruct H4 as [H4|[H4|H4]].
  - left. assumption.
  - right. left. apply E.Charac2. assumption.
  - right. right. apply E.Charac2. assumption.
Qed.

(* The order :< is founded on any class A.                                      *)
Proposition IsFounded : forall (A:Class),
  Founded E A.
Proof.
  intros A. apply Founded.InclCompat with V.
  - apply V.IsIncl.
  - apply E.IsFounded.
Qed.

(* The order :< is a strict order on any class of ordinals.                     *)
Proposition IsStrictOrd : forall (A:Class),
  A :<=: On -> StrictOrd E A.
Proof.
  intros A H1. split.
  - apply IsIrreflexive.
  - apply IsTransitive. assumption.
Qed.

(* The order :< is a strict total order on any class of ordinals.               *)
Proposition IsStrictTotalOrd : forall (A:Class),
  A :<=: On -> StrictTotalOrd E A.
Proof.
  intros A H1. split.
  - apply IsStrictOrd. assumption.
  - apply IsTotal. assumption.
Qed.

(* The order :< is well founded on any class A.                                 *)
Proposition IsWellFounded : forall (A:Class),
  WellFounded E A.
Proof.
  intros A. apply WellFounded.InclCompat with V.
  - apply V.IsIncl.
  - apply E.IsWellFounded.
Qed.

(* The order :< is a well ordering on any class of ordinals.                    *)
Proposition IsWellOrdering : forall (A:Class),
  A :<=: On -> WellOrdering E A.
Proof.
  intros A H1. split.
  - apply IsFounded.
  - apply IsTotal. assumption.
Qed.

(* The order :< is a well founded well ordering on any class of ordinals.       *)
Proposition IsWellFoundedOrd : forall (A:Class),
  A :<=: On -> WellFoundedWellOrd E A.
Proof.
  intros A H1. split.
  - apply IsWellFounded.
  - apply IsWellOrdering. assumption.
Qed.
