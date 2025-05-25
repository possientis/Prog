Require Import ZF.Class.Core.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Inter.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.

(* This is a more general treatment of ZF.Set.Inter where we allow the argument *)
(* of inter to be a class rather than a set. We do not introduce a notation.    *)

(* We consider the set defined by the (tweaked) intersection of A.              *)
Definition inter (A:Class) : U := fromClass :J(A) (IsSmall' A).

(* Characterisation of the elements of the intersection of A.                   *)
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

Proposition EquivCompat : forall (A B:Class),
  A :~: B -> inter A = inter B.
Proof.
  intros A B H1.
Admitted.

Proposition ToClass' : forall (A:Class),
  :J(A) :~: toClass (inter A).
Proof.
  intros A x. split; intros H1.
  - apply FromClass.Charac. assumption.
  - apply FromClass.Charac in H1. assumption.
Qed.

Proposition IsZero : inter :0: = :0:.
Proof.
  apply DoubleInclusion. split; intros x H1.
  - apply FromClass.Charac in H1. destruct H1 as [_ [y H1]]. contradiction.
  - apply ZF.Set.Empty.Charac in H1. contradiction.
Qed.

