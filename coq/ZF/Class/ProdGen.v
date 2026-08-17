
Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.FunctionOn.

Require Import ZF.Notation.ProdGen.
Export ZF.Notation.ProdGen.

(* The generalized product prd_{x :< a} A(x).                                   *)
Definition prodGen (a:U) (A:Class) : Class := fun f =>
  FunctionOn f a /\ forall x, x :< a -> f!x :< A!x.

(* Notation ":prd:_{ a } A" := (prodGen a A)                                    *)
Global Instance ProdGenClass : ProdGen U Class Class := { prodGen := prodGen }.

