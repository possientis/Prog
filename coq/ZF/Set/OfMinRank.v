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

(* The class of elements of A of minimal rank equals the corresponding class.   *)
Proposition ToClass : forall (A:Class),
  toClass (ofMinRank A) :~: CMR.ofMinRank A.
Proof.
  intros A. apply FromClass.ToClass.
Qed.

(* x has minimal rank in A iff x is in A and rank x <= rank y for all y in A.   *)
Proposition Charac : forall (A:Class) (x:U),
  x :< ofMinRank A <-> A x /\ forall y, A y -> rank x :<=: rank y.
Proof.
  intros A x. split; intro H1.
  - apply FromClass.Charac in H1. assumption.
  - apply FromClass.Charac. assumption.
Qed.

(* The set of minimal-rank elements of A is included in A.                      *)
Proposition IsIncl : forall (A:Class), toClass (ofMinRank A) :<=: A.
Proof.
  intros A x H1. apply Charac in H1. apply H1.
Qed.

(* If A is non-empty, the set of its minimal-rank elements is also non-empty.   *)
Proposition IsNotEmpty : forall (A:Class),
  A :<>: :0: -> ofMinRank A <> :0:.
Proof.
  intros A H1 H2.
  apply Empty.EmptyToClass in H2.
  apply CMR.IsNotEmpty with A. 1: assumption.
  apply Equiv.Tran with (toClass (ofMinRank A)). 2: assumption.
  apply Equiv.Sym, ToClass.
Qed.

(* If A is empty, then the set of its minimal-rank elements is the empty set.   *)
Proposition WhenZero : forall (A:Class),
  A :~: :0: -> ofMinRank A = :0:.
Proof.
  intros A H1.
  apply Empty.EmptyToClass, Equiv.Tran with (CMR.ofMinRank A).
  - apply ToClass.
  - apply CMR.WhenZero. assumption.
Qed.

Proposition SameRank : forall (A:Class) (x y:U),
  x :< ofMinRank A -> y :< ofMinRank A -> rank x = rank y.
Proof.
  intros A x y H1 H2. apply Incl.Double. split.
  - apply (Charac A x). 1: assumption. apply IsIncl. assumption.
  - apply (Charac A y). 1: assumption. apply IsIncl. assumption.
Qed.

