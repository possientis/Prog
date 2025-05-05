Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Inter.
Require Import ZF.Set.Core.
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
Admitted.
(*
  intros a b H1 H2. apply Incl.EquivCompatR with :U(toClass a).
  - apply Union.ToClass.
  - apply Class.Ordinal.Union.IsUpperBound; assumption.
Qed.

(* The union of a set of ordinals is the smallest 'upper-bound'.                *)
Proposition IsSmallest : forall (a b:U),
  toClass a :<=: Ordinal          ->
  Ordinal b                       ->
  (forall c, c :< a -> c :<=: b)  ->
  :U(a) :<=: b.
Proof.
  intros a b H1 H2 H3. apply Incl.EquivCompatL with :U(toClass a).
  - apply Union.ToClass.
  - apply Class.Ordinal.Union.IsSmallest; assumption.
Qed.
*)
