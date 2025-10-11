Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.E.
Require Import ZF.Class.Ordinal.Order.
Require Import ZF.Class.Ordinal.Recursion.
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

Show.

