Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Function.
Require Import ZF.Class.Functional.
Require Import ZF.Class.OneToOne.
Require Import ZF.Class.Range.
Require Import ZF.Class.Relation.
Require Import ZF.Set.
Require Import ZF.Set.Eval.


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

Proposition BijectionFEvalIsInRange : forall (F:Class) (x:U),
  Bijection F -> domain F x -> range F (F!x).
Proof.
  intros F x H1 H2. apply FunctionFEvalIsInRange. 2: assumption.
  apply BijectionIsFunction. assumption.
Qed.

Proposition BijectionF_EvalIsInDomain : forall (F:Class) (y:U),
  Bijection F -> range F y -> domain F (F^:-1:!y).
Proof.
  intros F y H1 H2. apply ConverseRange, BijectionFEvalIsInRange.
  - apply ConverseIsBijection. assumption.
  - apply ConverseDomain. assumption.
Qed.

Proposition BijectionF_FEval : forall (F:Class) (x:U),
  Bijection F -> domain F x -> F^:-1:!(F!x) = x.
Proof.
  intros F x [_ H1]. apply OneToOneF_FEval. assumption.
Qed.

Proposition BijectionFF_Eval : forall (F:Class) (y:U),
  Bijection F -> range F y -> F!(F^:-1:!y) = y.
Proof.
  intros F y [_ H1]. apply OneToOneFF_Eval. assumption.
Qed.
