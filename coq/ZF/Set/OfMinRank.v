Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.OfMinRank.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Rank.

Module CEM := ZF.Class.Empty.
Module CMR := ZF.Class.OfMinRank.


(* The set of elements of the class A with minimal rank.                        *)
Definition ofMinRank (A:Class) : U := fromClass (CMR.ofMinRank A) (CMR.IsSmall A).

Proposition ToClass : forall (A:Class),
  toClass (ofMinRank A) :~: CMR.ofMinRank A.
Proof.
  intros A. apply FromClass.ToFromClass.
Qed.

Proposition Charac : forall (A:Class) (x:U),
  x :< ofMinRank A <-> A x /\ forall y, A y -> rank x :<=: rank y.
Proof.
  intros A x. split; intro H1.
  - apply FromClass.Charac in H1. assumption.
  - apply FromClass.Charac. assumption.
Qed.

Proposition IsIncl : forall (A:Class), toClass (ofMinRank A) :<=: A.
Proof.
  intros A x H1. apply Charac in H1. apply H1.
Qed.

Proposition IsNotEmpty : forall (A:Class),
  A :<>: :0: -> ofMinRank A <> :0:.
Proof.
  intros A H1 H2.
  apply Empty.EmptyToClass in H2.
  apply CMR.IsNotEmpty with A. 1: assumption.
  apply Equiv.Tran with (toClass (ofMinRank A)). 2: assumption.
  apply Equiv.Sym, ToClass.
Qed.

Proposition WhenZero : forall (A:Class),
  A :~: :0: -> ofMinRank A = :0:.
Proof.
  intros A H1.
  apply Empty.EmptyToClass, Equiv.Tran with (CMR.ofMinRank A).
  - apply ToClass.
  - apply CMR.WhenZero. assumption.
Qed.
