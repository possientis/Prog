Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Less.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Union.
Require Import ZF.Class.Small.
Require Import ZF.Class.Union.
Require Import ZF.Set.Core.

(* The supremum of the class A.                                                 *)
Definition sup (A:Class) : Class := :U(A :/\: On).

(* The supremum operation is compatible with class equivalence.                 *)
Proposition EquivCompat : forall (A B:Class),
  A :~: B -> sup A :~: sup B.
Proof.
  intros A B H1. apply Union.EquivCompat, Inter2.EquivCompatL. assumption.
Qed.

(* The supremum of a class of ordinals coincide with its union.                 *)
Proposition WhenHasOrdinalElem : forall (A:Class),
  A :<=: On -> sup A :~: :U(A).
Proof.
  intros A H1. unfold sup. apply Union.EquivCompat.
  intros x. split; intros H2.
  - apply H2.
  - split. 1: assumption. apply H1. assumption.
Qed.

(* The supremum of a class is an ordinal class.                                 *)
Proposition IsOrdinal : forall (A:Class), Ordinal (sup A).
Proof.
  intros A. apply Ordinal.Union.IsOrdinal, Class.Inter2.IsInclR.
Qed.

(* The supremum of a class is either the class of ordinals, or it is small.     *)
Proposition IsOnOrSmall : forall (A:Class),
  sup A :~: On \/ Small (sup A).
Proof.
  intros A. apply Core.IsOnOrSmall, IsOrdinal.
Qed.

(* The supremum is either the class of ordinals or a subclass thereof.          *)
Proposition IsOnOrLess : forall (A:Class),
  sup A :~: On \/ sup A :<: On.
Proof.
  intros A. apply Core.IsOnOrLess, IsOrdinal.
Qed.

(* The supremum of a class of ordinals is an upper-bound of that class.         *)
Proposition IsUpperBound : forall (A:Class) (a:U),
  A :<=: On -> A a -> toClass a :<=: sup A.
Proof.
  intros A a H1 H2. apply Incl.EquivCompatR with :U(A).
  - apply EquivSym, WhenHasOrdinalElem. assumption.
  - apply Ordinal.Union.IsUpperBound; assumption.
Qed.

(* The supremum of a class of ordinals is its smallest upper-bound.             *)
Proposition IsSmallest : forall (A:Class) (a:U),
  A :<=: On                   ->
  (forall b, A b -> b :<=: a) ->
  sup A :<=: toClass a.
Proof.
  intros A a H1 H2. apply Incl.EquivCompatL with :U(A).
  - apply EquivSym, WhenHasOrdinalElem. assumption.
  - apply Ordinal.Union.IsSmallest; assumption.
Qed.

Proposition IsOn : sup On :~: On.
Proof.
  apply EquivTran with :U(On).
  - apply WhenHasOrdinalElem, InclRefl.
  - apply Ordinal.Union.IsOn.
Qed.

