Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Recursion2.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Set.Core.


(* An ordinal function is a function with ordinal domain and ordinal values.    *)
Definition OrdFun (F:Class) : Prop
  := Function F /\ Ordinal (domain F) /\ range F :<=: On.

Proposition RecursionOrdFun : forall (F:Class) (a:U),
  On a                      ->
  OrdFun F                  ->
  domain F :~: On           ->
  OrdFun (Recursion F a).
Proof.
Admitted.
