Require Import ZF.Axiom.Classic.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Union.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Union.

(* The union of an ordinal is an ordinal.                                       *)
Proposition IsOrdinal : forall (a:U), Ordinal a ->
  Ordinal :U(a).
Proof.
  intros a H1. apply Union.IsOrdinal.
  apply Core.IsLess. assumption.
Qed.

(* The union of an ordinal is an upper-bound of its elements.                   *)
Proposition IsUpperBound : forall (a b:U), Ordinal a ->
  b :< a -> b :<=: :U(a).
Proof.
  intros a b H1 H2. apply Union.IsUpperBound. 2: assumption.
  apply Core.IsLess. assumption.
Qed.

(* The union of an ordinal is the smallest upper-bound.                         *)
Proposition IsSmallest : forall (a b:U),
  Ordinal a                      ->
  (forall c, c :< a -> c :<=: b) ->
  :U(a) :<=: b.
Proof.
  intros a b H1 H2. apply Union.IsSmallest; try assumption.
  apply Core.IsLess. assumption.
Qed.

(* The union of an ordinal is not an element of it iff it is equal to it.       *)
Proposition NotElemIsEqual : forall (a:U), Ordinal a ->
  ~ :U(a) :< a <-> :U(a) = a.
Proof.
  intros a H1. split; intros H2.
  - apply DoubleInclusion. split.
    + apply IsSmallest; try assumption.
      intros c H3. apply IfElemThenIncl; try assumption.
      apply Core.IsOrdinal with a; assumption.
    + assert (:U(a) :< a \/ a :<=: :U(a)) as H3. {
        apply ElemOrIncl. 2: assumption.
        apply IsOrdinal. assumption. }
      destruct H3 as [H3|H3]. 1: contradiction. assumption.
  - intros H3. rewrite H2 in H3. apply NoElemLoop1 with a. assumption.
Qed.

(* The union of an ordinal is a subset of it.                                   *)
Proposition IsIncl : forall (a:U), Ordinal a ->
  :U(a) :<=: a.
Proof.
  intros a H1. assert (:U(a) :< a \/ ~ :U(a) :< a) as H2. {
    apply LawExcludedMiddle. }
  destruct H2 as [H2|H2].
  - apply IfElemThenIncl; try assumption. apply IsOrdinal.
    assumption.
  - apply NotElemIsEqual in H2. 2: assumption.
    rewrite H2. apply InclRefl.
Qed.
