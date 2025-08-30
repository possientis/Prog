Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.Induction.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Set.Core.
Require Import ZF.Set.Order.InitSegment.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Restrict.

Module COI := ZF.Class.Order.InitSegment.
Module SOI := ZF.Set.Order.InitSegment.

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
  WellFoundedWellOrd R A                                                  ->
  A a                                                                     ->
  A b                                                                     ->
  R :(a,b):                                                               ->
  FunctionOn f (initSegment R A a)                                        ->
  FunctionOn g (initSegment R A b)                                        ->
  (forall x, x :< initSegment R A a -> f!x = F!(f:|:initSegment R A x))   ->
  (forall x, x :< initSegment R A b -> g!x = F!(g:|:initSegment R A x))   ->
  (forall x, x :< initSegment R A a -> f!x = g!x).
Proof.
  intros R A F f g a b H1 H2 H3 H4 H5 H6 H7 H8.
  assert (forall x c, A c -> x :< initSegment R A c -> A x) as H9. {
    intros x c H9 H10. apply (SOI.IsIncl R A A c) in H10; try assumption.
    - apply H1.
    - apply Class.Incl.Refl. }
  remember (fun x => A x /\ (x :< initSegment R A a -> f!x = g!x)) as B eqn:H10.
  assert (A :~: B) as H11. {
    apply Induction with R. 1: assumption.
    - intros x H11. rewrite H10 in H11. destruct H11 as [H11 _]. assumption.
    - intros c H11. rewrite H10.
Admitted.
