Require Import ZF.Class.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Intersect.
Require Import ZF.Class.Relation.
Require Import ZF.Class.Small.
Require Import ZF.Class.Union.
Require Import ZF.Core.And.
Require Import ZF.Core.Or.
Require Import ZF.Set.Relation.

Definition CRelation := ZF.Class.Relation.Relation.
Definition SRelation := ZF.Set.Relation.Relation.

Proposition SmallIntersectSmall1 : forall (P Q:Class),
  Small P -> Small (P:/\:Q).
Proof.
  intros P Q [a Ha].
  apply BoundedClassIsSmall. exists a.
  intros x [H1 _]. apply Ha, H1.
Qed.

Proposition SmallIntersectSmall2 : forall (P Q:Class),
  Small Q -> Small (P:/\:Q).
Proof.
  intros P Q [a Ha]. apply BoundedClassIsSmall. exists a.
  intros x [_ H1]. apply Ha, H1.
Qed.

(* The union of two relation class is a relation class.                         *)
Proposition UnionRelIsRel : forall (P Q:Class),
  CRelation P -> CRelation Q -> CRelation (P:\/:Q).
Proof.
  intros P Q Hp Hq x H1. destruct H1 as [H1|H1].
  - apply Hp, H1.
  - apply Hq, H1.
Qed.

(* The union of a class of relations is a relation class.                       *)
Proposition UnionClassOfRelsIsRel : forall (P:Class),
  (forall x, P x -> SRelation x) -> CRelation :U(P).
Proof.
  intros P H1 x H2. unfold unionClass in H2. destruct H2 as [y [H2 H3]].
  apply H1 in H3. apply H3, H2.
Qed.
