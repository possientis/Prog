Require Import ZF.Class.
Require Import ZF.Class.Bijection.
Require Import ZF.Class.BijectionOn.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Range.
Require Import ZF.Class.Restrict.
Require Import ZF.Set.
Require Import ZF.Set.Eval.

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

Proposition BijEvalIsInRange : forall (F A B:Class) (x:U),
  Bij F A B -> A x -> B (F!x).
Proof.
  intros F A B x [H1 H2] H3. apply H2.
  apply BijectionOnEvalIsInRange with A; assumption.
Qed.

Proposition BijConverseEvalIsInDomain : forall (F A B:Class) (y:U),
  Bij F A B -> B y -> A (F^:-1:!y).
Proof.
  intros F A B y H1 H2. apply BijEvalIsInRange with B. 2: assumption.
  apply ConverseIsBij. assumption.
Qed.
