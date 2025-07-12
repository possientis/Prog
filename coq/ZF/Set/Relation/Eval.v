Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.Range.

Export ZF.Notation.Eval.

Definition eval (f a:U) : U := (toClass f)!a.

(* Notation "f ! a" := (eval f a)                                               *)
Global Instance SetEval : Eval U := { eval := eval }.

Proposition WhenNotInDomain : forall (f x:U), 
  ~ x :< domain f -> f!x = :0:.
Proof.
  intros f x H1. apply EvalOfClass.WhenNotInDomain. intros H2.
  apply H1. apply ZF.Set.Relation.Domain.ToClass. assumption. 
Qed.

(* If f is functional and a lies in domain of f then (a,y) :< f iff f!a = y.    *)
Proposition Charac : forall (f a y:U),
  Functional f -> a :< domain f -> :(a,y): :< f  <-> f!a = y.
Proof.
  intros f a y H1 H2. apply (EvalOfClass.Charac (toClass f)).
  - assumption.
  - apply Domain.ToClass. assumption.
Qed.

(* If f is functional and a lies in domain of f then (a,f!a) lies in f.         *)
Proposition Satisfies : forall (f a:U),
  Functional f -> a :< domain f -> :(a,f!a): :< f.
Proof.
  intros f a H1 H2. apply Charac; try assumption. reflexivity.
Qed.

Proposition IsInRange : forall (f a:U),
  Functional f -> a :< domain f -> f!a :< range f.
Proof.
  intros f a H1 H2. apply Range.Charac. exists a. apply Satisfies; assumption.
Qed.

Proposition ImageCharac : forall (f a: U), Functional f ->
  forall y, y :< f:[a]: <-> exists x, x :< a /\ x :< domain f /\ f!x = y.
Proof.
  intros f a H1 y. split; intros H2.
  - apply Image.Charac in H2. destruct H2 as [x [H2 H3]].
    exists x. split. 1: assumption.
    assert (x :< domain f) as H4. { apply Domain.Charac. exists y. assumption. }
    split. 1: assumption. apply Charac; assumption.
  - destruct H2 as [x [H2 [H3 H4]]]. apply Image.Charac. exists x.
    split. 1: assumption. apply Charac; assumption.
Qed.

