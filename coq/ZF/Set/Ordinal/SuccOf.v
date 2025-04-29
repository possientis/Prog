Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.UnionOf.
Require Import ZF.Set.Union.

(* The successor of the union of an ordinal is an ordinal.                      *)
Proposition IsOrdinal : forall (a:U), Ordinal a ->
  Ordinal (succ :U(a)).
Proof.
  intros a H1. apply Succ.IsOrdinal, UnionOf.IsOrdinal. assumption.
Qed.

(* The successor of the union of a set of ordinals is a strict 'upper-bound'.   *)
Proposition IsStrictUpperBound : forall (a b:U),
  toClass a :<=: On ->
  b :< a            ->
  b :< succ :U(a).
Proof.
  intros a b H1 H2. apply InclElemTran with :U(a).
  - apply H1. assumption.
  - apply Union.IsOrdinal. assumption.
  - apply Succ.IsOrdinal, Union.IsOrdinal. assumption.
  - apply Union.IsUpperBound; assumption.
  - apply IsIn.
Qed.

(* The successor of the union of an ordinal is a strict upper-bound.            *)
Proposition IsStrictUpperBound2 : forall (a b:U),
  Ordinal a         ->
  b :< a            ->
  b :< succ :U(a).
Proof.
  intros a b H1. apply IsStrictUpperBound.
  apply Core.IsLess. assumption.
Qed.

(* An ordinal is a subset of the successor ot its union.                        *)
Proposition IsIncl : forall (a:U), Ordinal a ->
  a :<=: succ :U(a).
Proof.
  intros a H1 b. apply IsStrictUpperBound2. assumption.
Qed.

(* An ordinal is either equal to its union, or to the successor thereof.        *)
Proposition UnionOrSuccOfUnion : forall (a:U), Ordinal a ->
  a = :U(a) \/ a = succ :U(a).
Proof.
  intros a H1. apply DoubleNegation. intros H2.
  apply NoInBetween with :U(a) a. split.
  - apply LessIsElem. 2: assumption.
    + apply UnionOf.IsOrdinal. assumption.
    + split.
      * apply UnionOf.IsIncl. assumption.
      * intros H3. apply H2. left. symmetry. assumption.
  - apply LessIsElem. 1: assumption.
    + apply IsOrdinal. assumption.
    + split.
      * apply IsIncl. assumption.
      * intros H3. apply H2. right. assumption.
Qed.


