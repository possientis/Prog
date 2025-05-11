Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Inter.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter.
Require Import ZF.Set.Ordinal.Core.

(* The intersection of a set of ordinals is an ordinal.                         *)
Proposition IsOrdinal : forall (a:U),
  toClass a :<=: Ordinal -> Ordinal :I(a).
Proof.
  intros a H1. apply Class.Ordinal.Core.EquivCompat with :J(toClass a).
  - apply Inter.ToClass'.
  - apply Class.Ordinal.Inter.IsOrdinal'. assumption.
Qed.

(* The intersection of a set of ordinals is a 'lower-bound' of the set.         *)
Proposition IsLowerBound : forall (a b:U),
  toClass a :<=: Ordinal ->
  b :< a                 ->
  :I(a) :<=: b.
Proof.
  intros a b H1 H2. apply Incl.EquivCompatL with :J(toClass a).
  - apply ToClass'.
  - apply Class.Ordinal.Inter.IsLowerBound'; assumption.
Qed.

(* The intersection of a set of ordinals is the largest 'lower-bound'.          *)
Proposition IsLargest : forall (a b:U),
  toClass a :<=: Ordinal          ->
  a <> :0:                        ->
  (forall c, c :< a -> b :<=: c)  ->
  b :<=: :I(a).
Proof.
  intros a b H1 H2 H3. apply Incl.EquivCompatR with :J(toClass a).
  - apply Inter.ToClass'.
  - apply Class.Ordinal.Inter.IsLargest'; try assumption.
    apply Empty.NotEmptyToClass. assumption.
Qed.

(* The notion of intersection is interesting only for sets of ordinals.         *)
Proposition IsZero : forall (a:U), Ordinal a -> :I(a) = :0:.
Proof.
  intros a H1.
  assert (a = :0: \/ a <> :0:) as H2. {
    apply LawExcludedMiddle. }
  destruct H2 as [H2|H2].
  - subst. apply Inter.IsZero.
  - apply DoubleInclusion. split; intros x H3.
    + apply Inter.Charac with a. 1: assumption. apply Core.HasZero; assumption.
    + apply Empty.Charac in H3. contradiction.
Qed.
