Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.

(* This is not defined as an axiom to keep track of results which rely on it.   *)
Definition Choice : Prop := forall a, exists f,
  FunctionOn f a /\ forall x, x :< a -> x <> :0: -> f!x :< x.
