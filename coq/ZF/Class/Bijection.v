Require Import ZF.Class.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Function.
Require Import ZF.Class.Functional.
Require Import ZF.Class.OneToOne.
Require Import ZF.Class.Rel.

(* A class is a bijection if it is a relation and it is one-to-one.             *)
Definition Bijection (F:Class) : Prop := Rel F /\ OneToOne F.

Proposition BijectionIsFunction : forall (F:Class),
  Bijection F -> Function F.
Proof.
  intros F [H1 H2].
  apply OneToOneIsFunctionalBothWays in H2. destruct H2 as [H2 _].
  split; assumption.
Qed.

Proposition ConverseIsFunction : forall (F:Class),
  Bijection F -> Function (converse F).
Proof.
  intros F [H1 H2].
  apply OneToOneIsFunctionalBothWays in H2. destruct H2 as [_ H2].
  split. 2: assumption. apply ConverseIsRelation.
Qed.

Proposition ConverseIsBijection : forall (F:Class),
  Bijection F -> Bijection (converse F).
Proof.
  intros F [H1 H2]. split.
  - apply ConverseIsRelation.
  - apply ConverseIsOneToOne. assumption.
Qed.
