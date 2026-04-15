Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.OrdFun.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.


(* A strictly monotone ordinal function.                                        *)
Definition Monotone (f:U) : Prop := OrdFun f  /\ forall (a b:U),
  a :< domain f -> b :< domain f -> a :< b  -> f!a :< f!b.

Proposition IsIncl : forall (f a:U),
  Monotone f -> a :< domain f -> a :<=: f!a.
Proof.
Admitted.
