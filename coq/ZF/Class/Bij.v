Require Import ZF.Class.
Require Import ZF.Class.Bijection.
Require Import ZF.Class.BijectionOn.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Range.
Require Import ZF.Class.Restrict.

(* F is a bijection from A to B.                                                *)
Definition Bij (F A B:Class) : Prop := BijectionOn F A /\ range F :~: B.

Proposition ConverseIsBij : forall (F A B:Class),
  Bij F A B -> Bij F^:-1: B A.
Proof.
  intros F A B [[H1 H2] H3]. split.
  - split.
    + apply ConverseIsBijection. assumption.
    + apply ClassEquivTran with (range F). 2: assumption. apply ConverseDomain.
  - apply ClassEquivTran with (domain F). 2: assumption. apply ConverseRange.
Qed.
