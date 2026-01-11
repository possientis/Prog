Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.

Definition Decreasing (f:U) : Prop := forall (x y:U),
  x   :< domain f ->
  y   :< domain f ->
  x   :< y        ->
  f!y :< f!x.


