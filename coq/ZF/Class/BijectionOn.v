Require Import ZF.Class.
Require Import ZF.Class.Bijection.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Function.
Require Import ZF.Class.FunctionOn.
Require Import ZF.Class.Small.
Require Import ZF.Core.Equiv.

(* F is a bijection defined on A.                                               *)
Definition BijectionOn (F A:Class) : Prop := Bijection F /\ domain F :~: A.

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
