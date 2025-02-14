Require Import ZF.Class.
Require Import ZF.Class.Bijection.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Function.
Require Import ZF.Class.FunctionOn.
Require Import ZF.Class.Range.
Require Import ZF.Class.Restrict.
Require Import ZF.Class.Small.

(* F is a bijection defined on A.                                               *)
Definition BijectionOn (F A:Class) : Prop := Bijection F /\ domain F :~: A.

(* A bijection is always a bijection defined on its domain. *)
Proposition BijectionIsBijectionOn : forall (F:Class),
  Bijection F -> BijectionOn F (domain F).
Proof.
  intros F H1. split. { assumption. } { apply ClassEquivRefl. }
Qed.

(* A bijection defined on A is a function defined on A.                         *)
Proposition BijectionOnIsFunctionOn : forall (F A:Class),
  BijectionOn F A -> FunctionOn F A.
Proof.
  intros F A [H1 H2]. apply BijectionIsFunction in H1. split; assumption.
Qed.

(* A bijection defined on a small class is small.                               *)
Proposition BijectionOnIsSmall : forall (F A:Class),
  BijectionOn F A -> Small A -> Small F.
Proof.
  intros F A H1 H2. apply FunctionOnIsSmall with A. 2: assumption.
  apply BijectionOnIsFunctionOn. assumption.
Qed.

Proposition ConverseIsBijectionOn : forall (F A B:Class),
  BijectionOn F A -> range F :~: B -> BijectionOn F^:-1: B.
Proof.
  intros F A B [H1 H2] H3. split.
  - apply ConverseIsBijection. assumption.
  - apply ClassEquivTran with (range F). 2: assumption. apply ConverseDomain.
Qed.

Proposition BijectionOnIsRestrict : forall (F A:Class),
  BijectionOn F A -> F :~: F:|:A.
Proof.
  intros F A H1. apply FunctionOnIsRestrict, BijectionOnIsFunctionOn. assumption.
Qed.
