Require Import ZF.Class.
Require Import ZF.Class.Irreflexive.
Require Import ZF.Class.Transitive.

(* Predicate expressing the fact that R is a strict order class on A.           *)
Definition StrictOrd (R A:Class) : Prop := Irreflexive R A /\ Transitive R A.

Proposition StrictOrdIsIrreflexive : forall (R A:Class),
  StrictOrd R A -> Irreflexive R A.
Proof.
  intros R A H1. apply H1.
Qed.

Proposition StrictOrdIsTransitive : forall (R A:Class),
  StrictOrd R A -> Transitive R A.
Proof.
  intros R A H1. apply H1.
Qed.
