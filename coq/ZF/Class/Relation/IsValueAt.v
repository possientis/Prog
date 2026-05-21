Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.FunctionalAt.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that y is the value of F at a.                 *)
Definition IsValueAt (F:Class) (a y:U) : Prop := F :(a,y): /\ FunctionalAt F a.

(* IsValueAt is compatible with class equivalence.                              *)
Proposition EquivCompat : forall (F G:Class) (a y:U),
  F :~: G -> IsValueAt F a y -> IsValueAt G a y.
Proof.
  intros F G a y H1 [H2 H3]. split.
  - apply H1. assumption.
  - apply FunctionalAt.EquivCompat with F; assumption.
Qed.

(* When F is functional at a, y being a value of F at a reduces to F (a,y).     *)
Proposition WhenFunctionalAt : forall (F:Class) (a y:U),
  FunctionalAt F a -> IsValueAt F a y <-> F :(a,y):.
Proof.
  intros F a y H1. split; intros H2.
  - destruct H2 as [H2 _]. assumption.
  - split; assumption.
Qed.

(* When F is functional, y being a value of F at a reduces to F (a,y).          *)
Proposition WhenFunctional : forall (F:Class) (a y:U),
  Functional F -> IsValueAt F a y <-> F :(a,y):.
Proof.
  intros F a y H1. apply WhenFunctionalAt.
  apply IsFunctionalAt. assumption.
Qed.
