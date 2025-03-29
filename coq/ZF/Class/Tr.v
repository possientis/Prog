Require Import ZF.Class.
Require Import ZF.Class.Incl.
Require Import ZF.Set.
Require Import ZF.Set.Foundation.

(* Predicate defining a transitive class.                                       *)
Definition Tr (A:Class) : Prop := forall x, A x -> toClass x :<=: A.

Proposition ElemIsStrictSubClass : forall (A:Class) (a:U),
  Tr A -> A a -> toClass a :<: A.
Proof.
  intros A a H1 H2. split.
  - apply H1. assumption.
  - intros H3. apply NoElemLoop1 with a. apply H3. assumption.
Qed.
