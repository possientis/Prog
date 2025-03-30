Require Import ZF.Class.
Require Import ZF.Class.Incl.
Require Import ZF.Set.
Require Import ZF.Set.Foundation.

(* Predicate defining a transitive class. Informally: y :< x :< A -> y:< A.     *)
Definition Transitive (A:Class) : Prop := forall x, A x -> toClass x :<=: A.

(* An element of a transitive class defines a strict subclass of that class.    *)
Proposition ElemIsStrictSubclass : forall (A:Class) (a:U),
  Transitive A -> A a -> toClass a :<: A.
Proof.
  intros A a H1 H2. split.
  - apply H1. assumption.
  - intros H3. apply NoElemLoop1 with a. apply H3. assumption.
Qed.

(* Being a transitive class is compatible with class equivalence.               *)
Proposition EquivCompat : forall (A B:Class),
  A :~: B -> Transitive A -> Transitive B.
Proof.
  intros A B H1 H2 x H3. apply InclEquivCompatR with A. 1: assumption.
  apply H2, H1. assumption.
Qed.
