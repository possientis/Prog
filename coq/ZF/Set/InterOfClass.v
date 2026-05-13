Require Import ZF.Class.Equiv.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Inter.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.Pair.

Module CIR := ZF.Class.Inter.


(* We consider the set defined by the (tweaked) intersection of A.              *)
Definition inter (A:Class) : U := fromClass :I(A) (CIR.IsSmall A).

Proposition Charac : forall (A:Class) (x y:U),
  x :< inter A -> A y -> x :< y.
Proof.
  intros A x y H1 H2.
  apply FromClass.Charac in H1. destruct H1 as [H1 _]. apply H1. assumption.
Qed.

Proposition CharacRev : forall (A:Class) (x:U), A :<>: :0: ->
  (forall y, A y -> x :< y) -> x :< inter A.
Proof.
  intros A x H1 H2. apply FromClass.Charac. split. 1: assumption.
  apply Class.Empty.HasElem in H1. assumption.
Qed.

(* The intersection is compatible with class equivalence.                       *)
Proposition EquivCompat : forall (A B:Class),
  A :~: B -> inter A = inter B.
Proof.
  intros A B H1.
  apply FromClass.EquivCompat, Class.Inter.EquivCompat. assumption.
Qed.

(* The class of the intersection of A is the class-level intersection of A.     *)
Proposition ToClass : forall (A:Class),
  toClass (inter A) :~: :I(A).
Proof.
  intros A x. split; intros H1.
  - apply FromClass.Charac in H1. assumption.
  - apply FromClass.Charac. assumption.
Qed.

(* The intersection of the empty class is the empty set.                        *)
Proposition IsZero : inter :0: = :0:.
Proof.
  apply Incl.Double. split; intros x H1.
  - apply FromClass.Charac in H1. destruct H1 as [_ [y H1]]. contradiction.
  - apply ZF.Set.Empty.Charac in H1. contradiction.
Qed.

