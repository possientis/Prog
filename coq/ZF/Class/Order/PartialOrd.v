Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.AntiSymmetric.
Require Import ZF.Class.Order.Reflexive.
Require Import ZF.Class.Order.Transitive.

(* Predicate expressing the fact that R is a partial order class on A.          *)
Definition PartialOrd (R A:Class) : Prop
  := Reflexive R A /\ AntiSymmetric R A /\ Transitive R A.

Proposition PartialOrdIsReflexive : forall (R A:Class),
  PartialOrd R A -> Reflexive R A.
Proof.
  intros R A H1. apply H1.
Qed.

Proposition PartialOrdIsAntiSymmetric : forall (R A:Class),
  PartialOrd R A -> AntiSymmetric R A.
Proof.
  intros R A H1. apply H1.
Qed.

Proposition PartialOrdIsTransitive : forall (R A:Class),
  PartialOrd R A -> Transitive R A.
Proof.
  intros R A H1. apply H1.
Qed.
