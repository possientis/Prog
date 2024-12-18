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
Require Import ZF.Core.Pipe.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Restricting a class P to a class Q.                                          *)
Definition restrict (P Q:Class) : Class
  := fromBinary (Restrict.restrict (toBinary P) Q).

(* Notation "P :|: Q" := (restrict P Q)                                         *)
Global Instance ClassPipe : Pipe Class Class := { pipe := restrict }.

Proposition RestrictCharac : forall (P Q:Class) (x:U),
  (P:|:Q) x <-> exists y, exists z, x = :(y,z): /\ Q y /\ P :(y,z):.
Proof.
  intros P Q x. split; intros H1.
  - apply H1.
  - destruct H1 as [y [z [H2 [H3 H4]]]].
    unfold pipe, ClassPipe, restrict, fromBinary.
    unfold Binary.Restrict.restrict, toBinary.
    exists y. exists z. split.
    + assumption.
    + split; assumption.
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
  intros P. split; intros H1.
  - intros x. split; intros H2.
    + apply RestrictCharac in H2. destruct H2 as [y [z [H3 [_ H4]]]].
      rewrite H3. apply H4.
    + destruct (H1 x H2) as [y [z H3]]. apply RestrictCharac.
      exists y. exists z. split.
      * assumption.
      * split.
        { apply DomainCharac. exists z. subst. assumption. }
        { subst. assumption. }
  - intros x H2. apply DoubleInclusion in H1. destruct H1 as [_ H1].
    remember (H1 x) as H3 eqn:E. clear E H1. apply H3 in H2. clear H3.
    apply (proj1 (RestrictCharac _ _ _)) in H2. destruct H2 as [y [z [H2 _]]].
    exists y. exists z. assumption.
Qed.
