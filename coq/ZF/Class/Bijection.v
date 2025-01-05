Require Import ZF.Class.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Function.
Require Import ZF.Class.OneToOne.
Require Import ZF.Class.Rel.

(* A class is a bijection if it is a relation and it is one-to-one.             *)
Definition Bijection (F:Class) : Prop := Rel F /\ OneToOne F.

Proposition BijectionIsFunction : forall (F:Class),
  Bijection F -> Function F.
Proof.
  intros F [H1 [H2 H3]]. split; assumption.
Qed.

Proposition BijectionConverseIsFunction : forall (F:Class),
  Bijection F -> Function (converse F).
Proof.
  intros F [H1 [H2 H3]]. split.
  - apply ConverseIsRelation.
  - apply H3.
Qed.
