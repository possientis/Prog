Require Import ZF.Class.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Small.
Require Import ZF.Core.And.

(* The intersection of two classes P and Q.                                     *)
Definition intersect (P Q:Class) : Class := fun x => P x /\ Q x.

(* Notation "P :/\: Q" := (intersect P Q)                                       *)
Global Instance ClassAnd : And Class := { and := intersect }.

Proposition SmallIntersectSmallL : forall (P Q:Class),
  Small P -> Small (P:/\:Q).
Proof.
  intros P Q [a Ha].
  apply BoundedClassIsSmall. exists a.
  intros x [H1 _]. apply Ha, H1.
Qed.

Proposition SmallIntersectSmallR : forall (P Q:Class),
  Small Q -> Small (P:/\:Q).
Proof.
  intros P Q [a Ha]. apply BoundedClassIsSmall. exists a.
  intros x [_ H1]. apply Ha, H1.
Qed.
