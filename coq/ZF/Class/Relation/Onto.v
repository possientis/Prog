Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Relation.Fun.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.Range.

(* F is a surjective function class from A to B.                                *)
Definition Onto (F A B:Class) : Prop := FunctionOn F A /\ range F :~: B.

Proposition IsFun : forall (F A B:Class), Onto F A B -> Fun F A B.
Proof.
  intros F A B H1. split. 1: apply H1. apply DoubleInclusion, EquivSym, H1.
Qed.
