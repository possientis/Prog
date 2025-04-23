Require Import ZF.Class.Core.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.Range.

(* F is a surjective function class from A to B.                                *)
Definition Onto (F A B:Class) : Prop := FunctionOn F A /\ range F :~: B.
