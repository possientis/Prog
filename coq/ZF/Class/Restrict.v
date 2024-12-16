Declare Scope ZF_Class_Restrict_scope.

Require Import ZF.Binary.Restrict.
Require Import ZF.Class.
Require Import ZF.Class.Binary.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Image.
Require Import ZF.Class.Include.
Require Import ZF.Class.Intersect.
Require Import ZF.Class.Range.
Require Import ZF.Class.Relation.
Require Import ZF.Core.And.
Require Import ZF.Core.Equal.
Require Import ZF.Core.Leq.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

Open Scope    ZF_Class_Restrict_scope.

(* Restricting a class P to a class Q.                                          *)
Definition restrict (P Q:Class) : Class
  := fromBinary (Restrict.restrict (toBinary P) Q).

Notation "P :|: Q" := (restrict P Q)
  (at level 13, left associativity) : ZF_Class_Restrict_scope.

Proposition RestrictCharac : forall (P Q:Class) (x:U),
  (P:|:Q) x -> exists y, exists z, x = :(y,z): /\ Q y /\ P :(y,z):.
Proof.
  intros P Q x H1. apply H1.
Qed.

Proposition RestrictCharac2 : forall (P Q:Class) (y z:U),
  (P:|:Q) :(y,z): <-> Q y /\ P :(y,z):.
Proof.
  intros P Q y z. split; intros H1.
  - apply RestrictCharac in H1.
    destruct H1 as [y' [z' [H1 H2]]]. apply OrdPairEqual in H1.
    destruct H1 as [H1 H1']. subst. apply H2.
  - exists y. exists z. split.
    + reflexivity.
    + apply H1.
Qed.

Proposition RestrictIsRelation : forall (P Q:Class),
  Relation (P:|:Q).
Proof.
  intros P Q. apply FromBinaryIsRelation.
Qed.

Proposition DomainOfRestrict : forall (P Q:Class),
  domain (P:|:Q) :~: Q :/\: domain P.
Proof.
  intros P Q x. split; intros H1.
  - apply (proj1 (DomainCharac (P:|:Q) x)) in H1. destruct H1 as [y H1].
    apply RestrictCharac2 in H1. destruct H1 as [H1 H2]. split.
    + apply H1.
    + apply DomainCharac. exists y. apply H2.
  - destruct H1 as [H1 H2]. apply (proj1 (DomainCharac P x)) in H2.
    destruct H2 as [y H2]. apply DomainCharac. exists y. apply RestrictCharac2.
    split; assumption.
Qed.

Proposition ImageIsRangeOfRestrict : forall (P:Class) (a:U),
  P:[a]: :~: range (P:|:(toClass a)).
Proof.
  intros P a y. split; intros H1.
  - apply ImageCharac in H1. destruct H1 as [x [H1 H2]].
    exists x. unfold toBinary. apply RestrictCharac2. split; assumption.
  - apply RangeCharac in H1. destruct H1 as [x H1]. apply RestrictCharac2 in H1.
    destruct H1 as [H1 H2]. exists x. unfold toBinary. split; assumption.
Qed.

Proposition RestrictIsSubClass : forall (P Q:Class),
  P:|:Q :<=: P.
Proof.
  intros P Q x H1. apply RestrictCharac in H1. destruct H1 as [y [z [H1 [_ H2]]]].
  rewrite H1. apply H2.
Qed.

Proposition RestrictToDomain : forall (P:Class),
  Relation P <-> P :|: domain P :~: P.
Proof.
Admitted.
