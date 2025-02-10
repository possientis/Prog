Require Import ZF.Class.
Require Import ZF.Class.BijectionOn.
Require Import ZF.Class.I.
Require Import ZF.Class.Range.
Require Import ZF.Class.Restrict.

(* F is a bijection from A to B.                                                *)
Definition Bij (F A B:Class) : Prop := BijectionOn F A /\ range F :~: B.

Proposition BijI : forall (A:Class), Bij (I:|:A) A A.
Proof.
  intros A. split.
  -
Admitted.
