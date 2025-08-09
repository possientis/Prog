Require Import ZF.Class.Equiv.
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

Proposition InterOn : forall (A:Class), sup A :~: sup (A :/\: On).
Proof.
  intros A.
  apply Union.EquivCompat, Equiv.Sym, Class.Inter2.WhenInclL, Class.Inter2.IsInclR.
Qed.

(* The supremum of a class of ordinals coincide with its union.                 *)
Proposition WhenOrdinalElem : forall (A:Class),
  A :<=: On -> :U(A) :~: sup A.
Proof.
  intros A H1. unfold sup. apply Union.EquivCompat.
  intros x. split; intros H2.
  - split. 1: assumption. apply H1. assumption.
  - apply H2.
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
  - apply WhenOrdinalElem. assumption.
  - apply Ordinal.Union.IsUpperBound; assumption.
Qed.

(* The supremum of a class is an upper-bound of its ordinals.                   *)
Proposition IsUpperBoundOrd : forall (A:Class) (a:U), On a ->
  A a -> toClass a :<=: sup A.
Proof.
  intros A a H1 H2. apply Incl.EquivCompatR with (sup (A :/\: On)).
  - apply Equiv.Sym, InterOn.
  - apply IsUpperBound.
    + apply Class.Inter2.IsInclR.
    + split; assumption.
Qed.

(* The supremum of a class of ordinals is its smallest upper-bound.             *)
Proposition IsSmallest : forall (A:Class) (a:U),
  A :<=: On                   ->
  (forall b, A b -> b :<=: a) ->
  sup A :<=: toClass a.
Proof.
  intros A a H1 H2. apply Incl.EquivCompatL with :U(A).
  - apply WhenOrdinalElem. assumption.
  - apply Ordinal.Union.IsSmallest; assumption.
Qed.

(* The supremum is the smallest of ordinal upper-bounds.                        *)
Proposition IsSmallestOrd : forall (A:Class) (a:U),
  (forall b, On b -> A b -> b :<=: a) ->
  sup A :<=: toClass a.
Proof.
  intros A a H1. apply Incl.EquivCompatL with (sup (A :/\: On)).
  - apply Equiv.Sym, InterOn.
  - apply IsSmallest.
    + apply Class.Inter2.IsInclR.
    + intros b [H2 H3]. apply H1; assumption.
Qed.

Proposition IsOn : sup On :~: On.
Proof.
  apply Equiv.Tran with :U(On).
  - apply Equiv.Sym, WhenOrdinalElem, Class.Incl.Refl.
  - apply Ordinal.Union.IsOn.
Qed.
