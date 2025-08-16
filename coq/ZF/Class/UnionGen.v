Require Import ZF.Class.Equiv.
Require Import ZF.Class.Union.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.

Require Import ZF.Notation.UnionGen.
Export ZF.Notation.UnionGen.

(* Defining the generalized union \/_{x in P} Q(x).                             *)
Definition unionGen (P Q:Class) : Class
  := :U( fun y => exists x, P x /\ y = Q!x ).

(* Notation ":\/:_{ P } Q" := (unionGen P Q)                                    *)
Global Instance ClassUnionGen : UnionGen Class Class := {unionGen := unionGen }.

Proposition Charac : forall (P Q:Class) (y:U),
  :\/:_{P} Q y <-> exists x, P x /\ y :< Q!x.
Proof.
  intros P Q y. split; intros H1.
  - destruct H1 as [q [H1 H2]]. destruct H2 as [x [H2 H3]].
    rewrite H3 in H1. exists x. split; assumption.
  - destruct H1 as [x [H1 H2]]. exists (eval Q x). split.
    + assumption.
    + exists x. split. { assumption. } { reflexivity. }
Qed.
