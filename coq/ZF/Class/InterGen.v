Require Import ZF.Class.Equiv.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Inter.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.

Require Import ZF.Notation.InterGen.
Export ZF.Notation.InterGen.

(* Defining the generalized intersection /\_{x in P} Q(x).                      *)
Definition interGen (P Q:Class) : Class
  := :I( fun y => exists x, P x /\ y = Q!x ).

(* Notation ":/\:_{ P } Q" := (interGen P Q)                                    *)
Global Instance ClassInterGen : InterGen Class Class := {interGen := interGen }.

Proposition Charac : forall (P Q:Class) (y:U), P :<>: :0: ->
  :/\:_{P} Q y <-> forall x, P x -> y :< Q!x.
Proof.
  intros P Q y H1. apply Class.Empty.HasElem in H1. split; intros H2.
  - destruct H2 as [H2 _]. intros x H3. apply H2. exists x.
    split. 1: assumption. reflexivity.
  - split.
    + intros z [x [H3 H4]]. subst. apply H2. assumption.
    + destruct H1 as [x H1]. exists Q!x. exists x.
      split. 1: assumption. reflexivity.
Qed.
