Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.MinFresh.
Require Import ZF.Class.Ordinal.Order.E.
Require Import ZF.Class.Ordinal.Recursion.
Require Import ZF.Class.Ordinal.WFWOIsom.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.RestrictOfClass.

Module CMF := ZF.Class.Ordinal.MinFresh.
Module COC := ZF.Class.Ordinal.Core.
Module COE := ZF.Class.Ordinal.Order.E.
Module CWI := ZF.Class.Ordinal.WFWOIsom.

(* MinFresh A picks the E-minimal element of A not yet in the range of its arg. *)
Definition MinFresh (A:Class) : Class := CMF.MinFresh E A.

(* The canonical isomorphism from On onto A when A is a subclass of On.         *)
Definition Enum (A:Class) : Class := Recursion (MinFresh A).

(* MinFresh A is a function class when A is a subclass of On.                   *)
Proposition IsFunction : forall (A:Class),
  A :<=: On -> Function (MinFresh A).
Proof.
  intros A H1. apply CMF.IsFunction, COE.IsTotal. assumption.
Qed.

(* Enum A is a function class defined on the class of ordinals.                 *)
Proposition IsFunctionOn : forall (A G:Class),
  G :~: Enum A -> FunctionOn G On.
Proof.
  intros A G H1. apply CWI.IsFunctionOn with E A. assumption.
Qed.

(* Enum A is MinFresh-recursive.                                                *)
Proposition IsRecursive : forall (A F G:Class),
  F :~: MinFresh A               ->
  G :~: Enum A                   ->
  forall a, On a -> G!a = F!(G:|:a).
Proof.
  intros A F G H1 H2. apply CWI.IsRecursive with E A; assumption.
Qed.

(* Enum A is an isomorphism from On to A.                                       *)
Proposition IsIsom : forall (A G:Class),
  Proper A                      ->
  A :<=: On                     ->
  G :~: Enum A                  ->
  Isom G E E On A.
Proof.
  intros A G H1 H2 H3. apply CWI.IsIsom; try assumption.
  apply COE.IsWellFoundedWellOrd. assumption.
Qed.

(* Enum A is the unique isomorphism from On to A.                               *)
Proposition IsUnique : forall (A G:Class),
  Proper A                        ->
  A :<=: On                       ->
  Isom G E E On A                 ->
  G :~: Enum A.
Proof.
  intros A G H1 H2 H3. apply CWI.IsUnique; try assumption.
  apply COE.IsWellFoundedWellOrd. assumption.
Qed.

(* A well ordered small class of ordinals is isomorphic to an ordinal.          *)
Proposition WhenSmall : forall (A:Class),
  Small A         ->
  A :<=: On       ->

  exists a, On a  /\
    forall (g:U),
      g = (Enum A :|: a) ->
      Isom (toClass g) E E (toClass a) A.
Proof.
  intros A H1 H2. apply CWI.WhenSmall. 1: assumption.
  apply COE.IsWellOrdering. assumption.
Qed.
