Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.

(* Predicate on classes, stating that a class is smaller than a set.            *)
Definition Bounded (A:Class) : Prop := exists a, forall x, A x -> x :< a.

(* A class is small if and only if it is bounded.                               *)
Proposition IsSmall : forall (A:Class),
  Bounded A <-> Small A.
Proof.
  intros A. split; intros H1; destruct H1 as [a H1].
  - apply Small.InclCompat with (toClass a).
    intros x. apply H1. apply SetIsSmall.
  - exists a. intros x H2. apply H1. assumption.
Qed.
