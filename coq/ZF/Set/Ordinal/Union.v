Require Import ZF.Class.
Require Import ZF.Class.Ordinal.
Require Import ZF.Set.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Union.

(* The union of a set of ordinals is an ordinal.                                *)
Proposition UnionIsOrdinal : forall (a:U),
  toClass a :<=: On -> Ordinal :U(a).
Proof.
  intros a H1. apply Class.Ordinal.EquivCompat with :U(toClass a).
  - apply UnionOfToClass.
  - apply Class.Ordinal.UnionIsOrdinal. assumption.
Qed.

(* The union of an ordinal is an ordinal.                                       *)
Proposition UnionOfOrdinalIsOrdinal : forall (a:U), Ordinal a ->
  Ordinal :U(a).
Proof.
  intros a H1. apply UnionIsOrdinal.
  apply OrdinalIsStrictSubclass. assumption.
Qed.

(* The union of a set of ordinals is an 'upper-bound' of the set.               *)
Proposition UnionIsUpperBound : forall (a b:U),
  toClass a :<=: On -> 
  b :< a            -> 
  b :<=: :U(a).
Proof.
  intros a b H1 H2. apply Incl.EquivCompatR with :U(toClass a).
  - apply UnionOfToClass.
  - apply Class.Ordinal.UnionIsUpperBound; assumption.
Qed.

(* The union of an ordinal is an upper-bound ot its elements.                   *)
Proposition UnionOfOrdinalIsUpperBound : forall (a b:U), Ordinal a -> 
  b :< a -> b :<=: :U(a). 
Proof.
  intros a b H1 H2. apply UnionIsUpperBound. 2: assumption.
  apply OrdinalIsStrictSubclass. assumption.
Qed.

(* The union of a set of ordinals is the smallest 'upper-bound'.                *)
Proposition UnionIsSmallestUpperBound : forall (a b:U),
  toClass a :<=: On               ->
  Ordinal b                       ->
  (forall c, c :< a -> c :<=: b)  ->
  :U(a) :<=: b.
Proof.
  intros a b H1 H2 H3. apply Incl.EquivCompatL with :U(toClass a).
  - apply UnionOfToClass.
  - apply Class.Ordinal.UnionIsSmallestUpperBound; assumption.
Qed.

(* The union of an ordinal is the smallest upper-bound.                         *)
Proposition UnionOfOrdinalIsSmallestUpperBound : forall (a b:U), 
  Ordinal a                      -> 
  Ordinal b                      ->
  (forall c, c :< a -> c :<=: b) -> 
  :U(a) :<=: b.
Proof.
  intros a b H1 H2 H3. apply UnionIsSmallestUpperBound; try assumption.
  apply OrdinalIsStrictSubclass. assumption. 
Qed.

Proposition UnionNotElemIsUnionEqual : forall (a:U), Ordinal a ->
  ~ :U(a) :< a <-> :U(a) = a.
Proof.
  intros a H1. split; intros H2.
  - apply DoubleInclusion. split.
    + apply UnionOfOrdinalIsSmallestUpperBound; try assumption.
      intros c H3. apply ElemIsIncl; try assumption.
      apply ElemIsOrdinal with a; assumption.
    + assert (:U(a) :< a \/ a :<=: :U(a)) as H3. {
        apply ElemOrIncl. 2: assumption. 
        apply UnionOfOrdinalIsOrdinal. assumption. }
      destruct H3 as [H3|H3]. 1: contradiction. assumption.
  - intros H3. rewrite H2 in H3. apply NoElemLoop1 with a. assumption.
Qed.
