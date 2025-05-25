Require Import ZF.Axiom.Define.
Require Import ZF.Class.Core.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.

(* The class of all sets defined by the predicate A.                            *)
Definition IsSetOf (A:Class) : Class := fun a =>
  forall x, x :< a <-> A x.

(* If a class is small, it defines at least one set.                            *)
Proposition Exists : forall (A:Class),
  Small A -> Define.Exists (IsSetOf A).
Proof.
  intros A H1. apply H1.
Qed.

(* A class defines at most one set.                                             *)
Proposition Unique : forall (A:Class), Define.Unique (IsSetOf A).
Proof.
  intros A a b H1 H2.
  apply EqualToClass. apply EquivTran with A.
  - intros x. apply H1.
  - apply EquivSym. intros x. apply H2.
Qed.

Proposition EquivCompat : forall (A B:Class),
  A :~: B -> IsSetOf A :~: IsSetOf B.
Proof.
  intros A B H1 a. split; intros H2 x; split; intros H3.
  - apply H1, H2. assumption.
  - apply H2, H1. assumption.
  - apply H1, H2. assumption.
  - apply H2, H1. assumption.
Qed.
