Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Union.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Union.

Module COC := ZF.Class.Ordinal.Core.
Module COU := ZF.Class.Ordinal.Union.

(* The union of a set of ordinals is an ordinal.                                *)
Proposition IsOrdinal : forall (a:U),
  toClass a :<=: Ordinal -> Ordinal :U(a).
Proof.
  intros a H1. apply COC.EquivCompat with :U(toClass a).
  - apply Union.ToClass.
  - apply COU.IsOrdinal. assumption.
Qed.

(* The union of a set of ordinals is an 'upper-bound' of the set.               *)
Proposition IsUpperBound : forall (a b:U),
  toClass a :<=: Ordinal ->
  b :< a                 ->
  b :<=: :U(a).
Proof.
  intros a b H1 H2. apply Incl.EquivCompatR with :U(toClass a).
  - apply Union.ToClass.
  - apply COU.IsUpperBound; assumption.
Qed.

(* The union of a set of ordinals is the smallest 'upper-bound'.                *)
Proposition IsSmallest : forall (a b:U),
  toClass a :<=: Ordinal          ->
  (forall c, c :< a -> c :<=: b)  ->
  :U(a) :<=: b.
Proof.
  intros a b H1 H2. apply Incl.EquivCompatL with :U(toClass a).
  - apply Union.ToClass.
  - apply COU.IsSmallest; assumption.
Qed.

