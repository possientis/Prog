Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.E.
Require Import ZF.Class.Ordinal.Order.
Require Import ZF.Class.Ordinal.Recursion.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.RestrictOfClass.

Module COO := ZF.Class.Ordinal.Order.
Module COE := ZF.Class.Ordinal.E.

(* The class A is intended to be a class of ordinals.                           *)
Definition SmallestFresh (A:Class) : Class := COO.SmallestFresh E A.

(* With appropriate assumptions, the isomorphism between On and A.              *)
Definition RecurseSmallestFresh (A:Class) : Class := Recursion (SmallestFresh A).

(* SmallestFresh is a function class.                                           *)
Proposition IsFunction : forall (A:Class),
  A :<=: On -> Function (SmallestFresh A).
Proof.
  intros A H1. apply COO.IsFunction, COE.IsTotal. assumption.
Qed.

(* RecurseSmallestFresh is a function class defined on the class of ordinals.   *)
Proposition IsFunctionOn : forall (A G:Class),
  G :~: RecurseSmallestFresh A  -> FunctionOn G On.
Proof.
  intros A G H1. apply COO.IsFunctionOn with E A. assumption.
Qed.

(* RecurseSmallestFresh is SmallestFresh-recursive.                             *)
Proposition IsRecursive : forall (A F G:Class),
  F :~: SmallestFresh A               ->
  G :~: RecurseSmallestFresh A        ->
  forall a, On a -> G!a = F!(G:|:a).
Proof.
  intros A F G H1 H2. apply COO.IsRecursive with E A; assumption.
Qed.

(* RecurseSmallestFresh is an isomorphism from On to A.                         *)
Proposition IsIsom : forall (A G:Class),
  Proper A                      ->
  A :<=: On                     ->
  G :~: RecurseSmallestFresh A  ->
  Isom G E E On A.
Proof.
  intros A G H1 H2 H3. apply COO.IsIsom; try assumption.
  apply COE.IsWellFoundedWellOrd. assumption.
Qed.

(* RecurseSmallestFresh is the unique isomorphism from On to A.                 *)
Proposition IsUnique : forall (A G:Class),
  Proper A                        ->
  A :<=: On                       ->
  Isom G E E On A                 ->
  G :~: RecurseSmallestFresh A.
Proof.
  intros A G H1 H2 H3. apply COO.IsUnique; try assumption.
  apply COE.IsWellFoundedWellOrd. assumption.
Qed.
