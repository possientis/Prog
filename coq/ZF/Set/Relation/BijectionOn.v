Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Bijection.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.Range.

(* f is a bijection defined on a.                                               *)
Definition BijectionOn (f a:U) : Prop := Bijection f /\ domain f = a.


(* A bijection defined on a is a function defined on a.                         *)
Proposition IsFunctionOn : forall (f a:U),
  BijectionOn f a -> FunctionOn f a.
Proof.
  intros f a [H1 H2]. subst.
  apply FunctionOn.FunctionIsFunctionOn, Bijection.IsFunction. assumption.
Qed.

(* Two bijections with the same domains and which coincide pointwise are equal. *)
Proposition EqualCharac : forall (f g a b:U),
  BijectionOn f a                  ->
  BijectionOn g b                  ->
  a = b                            ->
  (forall x, x :< a -> f!x = g!x)  ->
  f = g.
Proof.
  intros f g a b H1 H2.
  apply FunctionOn.EqualCharac; apply IsFunctionOn; assumption.
Qed.

Proposition ImageOfDomain : forall (f a:U),
  BijectionOn f a -> f:[a]: = range f.
Proof.
  intros f a H1. apply FunctionOn.ImageOfDomain, IsFunctionOn. assumption.
Qed.

Proposition IsIncl : forall (f a:U),
  BijectionOn f a -> f :<=: a :x: f:[a]:.
Proof.
  intros f a H1. apply FunctionOn.IsIncl, IsFunctionOn. assumption.
Qed.
