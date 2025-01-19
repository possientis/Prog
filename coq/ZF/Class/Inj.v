Require Import ZF.Class.
Require Import ZF.Class.BijectionOn.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Range.
Require Import ZF.Core.Leq.

(* F is an injective function class from A to B.                                *)
Definition Inj (F A B: Class) : Prop := BijectionOn F A /\ range F :<=: B.
