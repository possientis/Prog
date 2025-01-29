Require Import ZF.Class.
Require Import ZF.Class.BijectionOn.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Range.

(* F is an injective function class from A to B.                                *)
Definition Inj (F A B: Class) : Prop := BijectionOn F A /\ range F :<=: B.
