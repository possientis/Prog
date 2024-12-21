Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Function.
Require Import ZF.Class.OneToOne.
Require Import ZF.Class.Relation.
Require Import ZF.Core.Dot.

(* A class is a bijection if it is a relation and it is one-to-one.             *)
Definition Bijection (P:Class) : Prop := Relation P /\ OneToOne P.

Proposition BijectionIsFunction : forall (P:Class),
  Bijection P -> Function P.
Proof.
  intros P [H1 [H2 H3]]. split; assumption.
Qed.

Proposition BijectionConverseIsFunction : forall (P:Class),
  Bijection P -> Function (converse P).
Proof.
  intros P [H1 [H2 H3]]. split.
  - apply ConverseIsRelation.
  - apply H3.
Qed.

Proposition ConposeIsBijection : forall (P Q:Class),
  OneToOne P -> OneToOne Q -> Bijection (P :.: Q).
Proof.
  intros P Q Hp Hq. split.
  - apply ComposeIsRelation.
  - apply ComposeIsOneToOne; assumption.
Qed.
