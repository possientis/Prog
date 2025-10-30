Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

(* The successor function class.                                                *)
Definition Succ : Class := fun x => exists a, x = :(a,succ a):.

Proposition Charac2 : forall (x y:U), Succ :(x,y): <-> y = succ x.
Proof.
  intros x y. split; intros H1.
  - destruct H1 as [a H1]. apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H2].
    subst. reflexivity.
  - subst. exists x. reflexivity.
Qed.

Proposition Satisfies : forall (a:U), Succ :(a, succ a):.
Proof.
  intros a. apply Charac2. reflexivity.
Qed.

Proposition Domain : forall (a:U), domain Succ a.
Proof.
  intros a. exists (succ a). exists a. reflexivity.
Qed.

Proposition IsFunctional : Functional Succ.
Proof.
  intros x y z H1 H2. apply Charac2 in H1. apply Charac2 in H2.
  subst. reflexivity.
Qed.

Proposition Eval : forall (a:U), Succ!a = succ a.
Proof.
  intros a. apply EvalOfClass.Charac.
  - apply IsFunctional.
  - apply Domain.
  - apply Satisfies.
Qed.

