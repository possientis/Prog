Require Import ZF.Axiom.Choice.
Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Eval.

Proposition Choice : forall (A:Class) (a:U), Choice ->
  (forall x, x :< a -> exists y, A :(x,y):)  ->
  exists f, FunctionOn f a                   /\
  forall x, x :< a -> A :(x,f!x):.
Proof.
Admitted.
