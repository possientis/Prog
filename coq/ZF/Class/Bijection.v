Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Function.
Require Import ZF.Class.Functional.
Require Import ZF.Class.OneToOne.
Require Import ZF.Class.Relation.

(* A class is a bijection if it is a relation and it is one-to-one.             *)
Definition Bijection (F:Class) : Prop := Relation F /\ OneToOne F.

Proposition BijectionIsFunction : forall (F:Class),
  Bijection F -> Function F.
Proof.
  intros F [H1 H2].
  apply OneToOneCharac in H2. destruct H2 as [H2 _].
  split; assumption.
Qed.

Proposition ConverseIsFunction : forall (F:Class),
  Bijection F -> Function F^:-1:.
Proof.
  intros F [H1 H2].
  apply OneToOneCharac in H2. destruct H2 as [_ H2].
  split. 2: assumption. apply ConverseIsRelation.
Qed.

Proposition ConverseIsBijection : forall (F:Class),
  Bijection F -> Bijection F^:-1:.
Proof.
  intros F [H1 H2]. split.
  - apply ConverseIsRelation.
  - apply ConverseIsOneToOne. assumption.
Qed.

(* The composition of two one-to-one classes is a bijection class.              *)
Proposition ComposeIsBijection : forall (F G:Class),
  OneToOne F -> OneToOne G -> Bijection (G :.: F).
Proof.
  intros F G Hf Hg. split.
  - apply ComposeIsRelation.
  - apply ComposeIsOneToOne; assumption.
Qed.


(* The composition of two bijection classes is a bijection class.               *)
Proposition ComposeIsBijection2 : forall (F G:Class),
  Bijection F -> Bijection G -> Bijection (G :.: F).
Proof.
  intros F G [_ Hf] [_ Hg]. apply ComposeIsBijection; assumption.
Qed.

