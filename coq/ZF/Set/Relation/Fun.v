Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.Range.

Require Import ZF.Notation.Fun.
Export ZF.Notation.Fun.

(* f is a function from a to b.                                                 *)
Definition Fun (f a b:U) : Prop := FunctionOn f a /\ range f :<=: b.

(* Notation "f :: a :-> b" := (Fun f a b)                                       *)
Global Instance SetFun : Notation.Fun.Fun U U := { IsFun := Fun }.

(* Two functions with the same domains and which coincide pointwise are equal.  *)
Proposition EqualCharac : forall (f a b g c d:U),
  f :: a :-> b                     ->
  g :: c :-> d                     ->
  a = c                            ->
  (forall x, x :< a -> f!x = g!x)  ->
  f = g.
Proof.
  intros f a b g c d [H1 _] [H2 _]. apply FunctionOn.EqualCharac; assumption.
Qed.

(* The direct image of the domain is the range.                                 *)
Proposition ImageOfDomain : forall (f a b:U),
  f :: a :-> b -> f:[a]: = range f.
Proof.
  intros f a b [H1 _]. apply FunctionOn.ImageOfDomain. assumption.
Qed.

(* A function f:a -> b is a subset of axb.                                      *)
Proposition IsIncl : forall (f a b:U),
  f :: a :-> b -> f :<=: a :x: b.
Proof.
  intros f a b [H1 H2]. apply ZF.Set.Incl.Tran with (a :x: f:[a]:).
  - apply FunctionOn.IsIncl. assumption.
  - Admitted.


