Require Import ZF.Class.
Require Import ZF.Class.FunctionOn.
Require Import ZF.Class.Range.
Require Import ZF.Core.Equiv.

(* F is a surjective function class from A to B.                                *)
Definition Onto (F A B:Class) : Prop := FunctionOn F A /\ range F :~: B.
