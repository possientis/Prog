Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.OrdFun.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.

(* A Strictly monotone ordinal function.                                        *)
Definition Monotone (F:Class) : Prop := OrdFun F /\ forall (a b:U),
  domain F a  ->
  domain F b  ->
  a :< b      ->
  F!a :< F!b.
