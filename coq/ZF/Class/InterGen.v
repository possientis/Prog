Require Import ZF.Class.Equiv.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.

Require Import ZF.Notation.InterGen.
Export ZF.Notation.InterGen.

(* Defining the generalized intersection /\_{x in A} B(x).                      *)
Definition interGen (A B:Class) : Class
  := :I( fun y => exists x, A x /\ y = B!x ).

(* Notation ":/\:_{ A } B" := (interGen A B)                                    *)
Global Instance ClassInterGen : InterGen Class Class := {interGen := interGen }.

Proposition Charac : forall (A B:Class) (x y:U),
  :/\:_{A} B y ->
  A x          ->
  y :< B!x.
Proof.
  intros A B x y H1 H2. destruct H1 as [H1 H3]. apply H1. exists x.
  split. 1: assumption. reflexivity.
Qed.

Proposition CharacRev : forall (A B:Class) (y:U),
  A :<>: :0:                  ->
  (forall x, A x -> y :< B!x) ->
  :/\:_{A} B y.
Proof.
  intros A B y H1 H2. split.
  - intros z H3. destruct H3 as [x [H3 H4]]. subst. apply H2. assumption.
  - apply Class.Empty.HasElem in H1. destruct H1 as [x H1].
    exists B!x. exists x. split. 1: assumption. reflexivity.
Qed.

(* The generalized intersection is a small class.                               *)
Proposition IsSmall : forall (A B:Class),
  Small :/\:_{A} B.
Proof.
  intros A B. apply Inter.IsSmall.
Qed.

(* This is a consequence of the choice made when defining the intersection.     *)
Proposition WhenEmpty : forall (A B:Class),
  A :~: :0: -> :/\:_{A} B :~: :0:.
Proof.
  intros A B H1. apply Inter.WhenEmpty. intros y. split; intros H2.
  - destruct H2 as [x [H2 H3]]. apply H1 in H2. contradiction.
  - contradiction.
Qed.

