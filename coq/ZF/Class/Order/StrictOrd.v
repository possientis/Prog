Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Irreflexive.
Require Import ZF.Class.Order.Transitive.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

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

Proposition StrictOrdWhenLess : forall (R A:Class) (x y:U),
  A x           ->
  A y           ->
  StrictOrd R A ->
  R :(x,y):     ->
  ~ (x = y \/ R :(y,x): ).
Proof.
  intros R A a y H1 H2 [H3 H4] H5 H6. destruct H6 as [H6|H6].
  - subst. apply H3 with y; assumption.
  - apply H3 with a. 1: assumption. apply H4 with y; assumption.
Qed.
