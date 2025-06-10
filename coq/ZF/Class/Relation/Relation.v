Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Union2.
Require Import ZF.Set.OrdPair.

(* A relation class is a class whose elements are ordered pairs.                *)
Definition Relation (F:Class) : Prop :=
    forall x, F x -> exists y, exists z, x = :(y,z):.

(* A function is a subclass of the product of its domain and image thereof.     *)
Proposition IsIncl : forall (F:Class),
  Relation F -> F :<=: (domain F) :x: F:[domain F]:.
Proof.
  intros F H1 x H3. unfold Relation in H1. specialize (H1 x H3).
  destruct H1 as [y [z H1]]. exists y. exists z. split. 1: assumption. split.
  - exists z. subst. assumption.
  - exists y. split.
    + exists z. subst. assumption.
    + subst. assumption.
Qed.

(* The pairwise union of two relation classes is a relation class.              *)
Proposition Union2 : forall (F G:Class),
  Relation F -> Relation G -> Relation (F:\/:G).
Proof.
  intros F G Hp Hq x H1. destruct H1 as [H1|H1].
  - apply Hp, H1.
  - apply Hq, H1.
Qed.

