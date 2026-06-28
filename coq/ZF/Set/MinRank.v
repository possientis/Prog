Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.MinRank.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.OfMinRank.
Require Import ZF.Set.Rank.


Module CMR := ZF.Class.MinRank.

(* The minimal rank of the elements of A.                                       *)
Definition minRank (A:Class) : U := fromClass (CMR.minRank A) (CMR.IsSmall A).

Proposition ToClass : forall (A:Class),
  toClass (minRank A) :~: CMR.minRank A.
Proof.
  intros A x. split; intros H1.
  - apply FromClass.Charac in H1. assumption.
  - apply FromClass.Charac. assumption.
Qed.

Proposition Charac : forall (A:Class) (x:U),
  x :< minRank A <-> exists y, y :< ofMinRank A /\ x :< rank y.
Proof.
  apply ToClass.
Qed.

Proposition WhenZero : forall (A:Class),
  A :~: :0: -> minRank A = :0:.
Proof.
  intros A H1.
  apply Empty.EmptyToClass, Equiv.Tran with (CMR.minRank A).
  - apply ToClass.
  - apply CMR.WhenZero. assumption.
Qed.
