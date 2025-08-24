Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.WellOrdering.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.RestrictByClass.

Definition Recursion (R A F:Class) : Class := fun x => exists f a,
  x :< f                                                              /\
  A a                                                                 /\
  Function f                                                          /\
  toClass (domain f) :~: initSegment R A a                            /\
  (forall b, initSegment R A a b -> f!b = F!(f:|:initSegment R A b)).

Definition K (R A F:Class) : U -> U -> Prop := fun f a =>
  A a                                                                 /\
  Function f                                                          /\
  toClass (domain f) :~: initSegment R A a                            /\
  (forall b, initSegment R A a b -> f!b = F!(f:|:initSegment R A b)).

Lemma Charac2 : forall (R A F:Class) (x y:U),
  Recursion R A F :(x,y): <-> exists f a, :(x,y): :< f /\ K R A F f a.
Proof.
  intros R A F x y. split; intros H1; destruct H1 as [f [a [H1 H2]]];
  exists f; exists a; split; assumption.
Qed.

Lemma Coincide : forall (R A F:Class) (f g a b:U),
  WellOrdering R A                                                      ->
  A a                                                                   ->
  A b                                                                   ->
  R :(a,b):                                                             ->
  Function f                                                            ->
  Function g                                                            ->
  toClass (domain f) :~: initSegment R A a                              ->
  toClass (domain g) :~: initSegment R A b                              ->
  (forall x, initSegment R A a x  -> f!x = F!(f:|:initSegment R A x))   ->
  (forall x, initSegment R A b x  -> g!x = F!(g:|:initSegment R A x))   ->
  (forall x, initSegment R A a x  -> f!x = g!x).
Proof.
Admitted.
