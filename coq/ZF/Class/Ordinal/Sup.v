Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Less.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Union.
Require Import ZF.Class.Union.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.

Require Import ZF.Notation.SupBelow.
Export ZF.Notation.SupBelow.

(* The supremum of the class A.                                                 *)
Definition sup (A:Class) : Class := :U(A :/\: On).

(* The supremum of the class A below a.                                         *)
Definition supBelow (b:U)(A:Class) : Class := :U(A :/\: On :/\: toClass b).

(* Notation "sup(:< b ) A" := (supBelow b A)                                    *)
Global Instance ClassSupBelow : SupBelow Class := { supBelow := supBelow }.

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

Proposition IsOrdinalBelow : forall (A:Class) (b:U),
  Ordinal (sup(:< b) A).
Proof.
  intros A b. apply Ordinal.Union.IsOrdinal. intros x H1.
  destruct H1 as [H1 [H2 H3]]. assumption.
Qed.

Proposition IsSmallBelow : forall (A:Class) (b:U),
  Small (sup(:< b) A).
Proof.
  intros A b. apply Union.IsSmall, Inter2.IsSmallR, Inter2.IsSmallR.
  apply SetIsSmall.
Qed.

Proposition IsLessBelow : forall (A:Class) (b:U),
  sup(:< b) A :<: On.
Proof.
  intros A b.
  assert (sup(:< b) A :~: On \/ sup(:< b) A :<: On) as H1. {
    apply Core.IsEquivOrLess, IsOrdinalBelow. }
  destruct H1 as [H1|H1]. 2: assumption. exfalso.
  apply OnIsProper. apply Small.EquivCompat with (sup(:< b) A).
  1: assumption. apply IsSmallBelow.
Qed.

(*
Proposition IsequivOrLess : forall (A:Class),
  sup A :~: On \/ sup A :<: On.
Proof.
  intros A. apply Core.IsEquivOrLess, IsOrdinal.
Qed.
*)


