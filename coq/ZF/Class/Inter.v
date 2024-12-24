Require Import ZF.Class.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Small.
Require Import ZF.Core.And.
Require Import ZF.Set.

(* The intersection of two classes P and Q.                                     *)
Definition inter (P Q:Class) : Class := fun x => P x /\ Q x.

(* Notation "P :/\: Q" := (inter P Q)                                           *)
Global Instance ClassAnd : And Class := { and := inter }.

Proposition InterCharac : forall (P Q:Class) (x:U),
  (P:/\:Q) x <-> P x /\ Q x.
Proof.
  intros P Q x. split; intros H1; apply H1.
Qed.

Proposition SmallInterSmallL : forall (P Q:Class),
  Small P -> Small (P:/\:Q).
Proof.
  intros P Q [a Ha].
  apply BoundedClassIsSmall. exists a.
  intros x [H1 _]. apply Ha, H1.
Qed.

Proposition SmallInterSmallR : forall (P Q:Class),
  Small Q -> Small (P:/\:Q).
Proof.
  intros P Q [a Ha]. apply BoundedClassIsSmall. exists a.
  intros x [_ H1]. apply Ha, H1.
Qed.

