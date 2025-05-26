Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Less.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Union.
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
  intros A. apply Ordinal.Union.IsOrdinal, Class.Inter2.InclR.
Qed.

(* The supremum is either the class of ordinals or a subclass thereof.          *)
Proposition IsequivOrLess : forall (A:Class),
  sup A :~: On \/ sup A :<: On.
Proof.
  intros A. apply Core.IsEquivOrLess, IsOrdinal.
Qed.
