Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Less.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Union.
Require Import ZF.Class.Small.
Require Import ZF.Class.Union.
Require Import ZF.Set.Core.

Require Import ZF.Notation.SupBelow.
Export ZF.Notation.SupBelow.

(* The supremum of the class A below b.                                         *)
Definition supBelow (b:U)(A:Class) : Class := :U(A :/\: On :/\: toClass b).

(* Notation "sup(:< b ) A" := (supBelow b A)                                    *)
Global Instance ClassSupBelow : SupBelow Class := { supBelow := supBelow }.

(* The supremum of a class below b is an ordinal class.                         *)
Proposition IsOrdinal : forall (A:Class) (b:U),
  Ordinal (sup(:< b) A).
Proof.
  intros A b. apply Ordinal.Union.IsOrdinal. intros x H1.
  destruct H1 as [H1 [H2 H3]]. assumption.
Qed.

(* The supremum of a class below b is a small class.                            *)
Proposition IsSmall : forall (A:Class) (b:U),
  Small (sup(:< b) A).
Proof.
  intros A b. apply Union.IsSmall, Inter2.IsSmallR, Inter2.IsSmallR.
  apply SetIsSmall.
Qed.

(* The supremum of a class below b is a strict subclass of On.                  *)
Proposition IsLess : forall (A:Class) (b:U),
  sup(:< b) A :<: On.
Proof.
  intros A b.
  assert (sup(:< b) A :~: On \/ sup(:< b) A :<: On) as H1. {
    apply Core.IsOnOrLess, IsOrdinal. }
  destruct H1 as [H1|H1]. 2: assumption. exfalso.
  apply OnIsProper. apply Small.EquivCompat with (sup(:< b) A).
  1: assumption. apply IsSmall.
Qed.
