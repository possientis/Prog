Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.WellOrdering.
Require Import ZF.Set.Core.
Require Import ZF.Set.Order.InitSegment.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Restrict.

Definition Recursion (R A F:Class) : Class := fun x => exists f a,
  x :< f                                                                  /\
  A a                                                                     /\
  FunctionOn f (initSegment R A a)                                        /\
  (forall b, b :< initSegment R A a -> f!b = F!(f:|:initSegment R A b)).

Definition K (R A F:Class) : U -> U -> Prop := fun f a =>
  A a                                                                     /\
  FunctionOn f (initSegment R A a)                                        /\
  (forall b, b :< initSegment R A a -> f!b = F!(f:|:initSegment R A b)).

Lemma Charac2 : forall (R A F:Class) (x y:U),
  Recursion R A F :(x,y): <-> exists f a, :(x,y): :< f /\ K R A F f a.
Proof.
  intros R A F x y. split; intros H1; destruct H1 as [f [a [H1 H2]]];
  exists f; exists a; split; assumption.
Qed.

Lemma Coincide : forall (R A F:Class) (f g a b:U),
  WellOrdering R A                                                        ->
  A a                                                                     ->
  A b                                                                     ->
  R :(a,b):                                                               ->
  FunctionOn f (initSegment R A a)                                        ->
  FunctionOn g (initSegment R A b)                                        ->
  (forall x, x :< initSegment R A a -> f!x = F!(f:|:initSegment R A x))   ->
  (forall x, x :< initSegment R A b -> g!x = F!(g:|:initSegment R A x))   ->
  (forall x, x :< initSegment R A a -> f!x = g!x).
Proof.
Admitted.
