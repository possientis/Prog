Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.AntiSymmetric.
Require Import ZF.Class.Order.Reflexive.
Require Import ZF.Class.Order.Transitive.
Require Import ZF.Class.Order.Transport.
Require Import ZF.Class.Relation.Bij.

(* Predicate expressing the fact that R is a partial order class on A.          *)
Definition PartialOrd (R A:Class) : Prop
  := Reflexive R A /\ AntiSymmetric R A /\ Transitive R A.

Proposition IsReflexive : forall (R A:Class),
  PartialOrd R A -> Reflexive R A.
Proof.
  intros R A H1. apply H1.
Qed.

Proposition IsAntiSymmetric : forall (R A:Class),
  PartialOrd R A -> AntiSymmetric R A.
Proof.
  intros R A H1. apply H1.
Qed.

Proposition IsTransitive : forall (R A:Class),
  PartialOrd R A -> Transitive R A.
Proof.
  intros R A H1. apply H1.
Qed.

(* Partial order is preserved under transport by a bijection.                   *)
Proposition Transport : forall (F R S A B:Class),
  (S = transport F R A) -> Bij F A B -> PartialOrd R A -> PartialOrd S B.
Proof.
  (* Proof by Claude.                                                           *)
  intros F R S A B H1 H2 [H3 [H4 H5]]. split.
  - apply (Reflexive.Transport F R S A B); assumption.
  - split.
    + apply (AntiSymmetric.Transport F R S A B); assumption.
    + apply (Transitive.Transport F R S A B); assumption.
Qed.
