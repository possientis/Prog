Require Import ZF.Class.
Require Import ZF.Class.Incl.
Require Import ZF.Set.
Require Import ZF.Set.Foundation.

(* Predicate defining a transitive class.                                       *)
Definition Tr (A:Class) : Prop := forall x, A x -> toClass x :<=: A.

(* An element of a transitive class defines a strict subclass of that class.    *)
Proposition ElemIsStrictSubClass : forall (A:Class) (a:U),
  Tr A -> A a -> toClass a :<: A.
Proof.
  intros A a H1 H2. split.
  - apply H1. assumption.
  - intros H3. apply NoElemLoop1 with a. apply H3. assumption.
Qed.

(* Being a transitive class is compatible with class equivalence.               *)
Proposition TrEquivCompat : forall (A B:Class),
  A :~: B -> Tr A -> Tr B.
Proof.
  intros A B H1 H2 x H3. apply InclEquivCompatR with A. 1: assumption.
  apply H2, H1. assumption.
Qed.
