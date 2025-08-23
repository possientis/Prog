Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Restrict.

Module SFO := ZF.Set.Relation.FunctionOn.

(*
Definition Recursion (R A F:Class) : Class := fun x => exists f a,
  x :< f                                                              /\
  A a                                                                 /\
  SFO.FunctionOn f (initSegment R A a)                                /\
  (forall b, initSegment R A a b -> f!b = F!(f:|:initSegment R A b)). 
*)
