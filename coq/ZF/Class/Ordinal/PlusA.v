Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Plus.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

(* The function class x -> x + a. Needed to define oridnal multiplication.      *)
Definition PlusA (a:U) : Class := fun x => exists b, x = :(b,b :+: a):.

Proposition Charac2 : forall (a x y:U), PlusA a :(x,y): <-> y = x :+: a.
Proof.
  intros a x y. split; intros H1.
  - destruct H1 as [b H1]. apply OrdPair.WhenEqual in H1.
    destruct H1 as [H1 H2]. subst. reflexivity.
  - exists x. subst. reflexivity.
Qed.

Proposition Satisfies : forall (a b:U),
  PlusA a :(b,b :+: a):.
Proof.
  intros a b. apply Charac2. reflexivity.
Qed.

Proposition Domain : forall (a b:U), domain (PlusA a) b.
Proof.
  intros a b. exists (b :+: a). exists b. reflexivity.
Qed.

Proposition IsFunctional : forall (a:U), Functional (PlusA a).
Proof.
  intros a x y z H1 H2. apply Charac2 in H1. apply Charac2 in H2.
  subst. reflexivity.
Qed.

Proposition Eval : forall (a b:U), (PlusA a)!b = b :+: a.
Proof.
  intros a b. apply EvalOfClass.Charac.
  - apply IsFunctional.
  - apply Domain.
  - apply Satisfies.
Qed.

