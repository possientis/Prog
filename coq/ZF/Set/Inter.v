Require Import ZF.Axiom.Classic.
Require Import ZF.Axiom.Extensionality.
Require Import ZF.Class.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.Incl.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Union2.
Export ZF.Notation.And.

(* The intersection of two sets a and b.                                        *)
Definition inter (a b:U) : U := fromClass (toClass a :/\: toClass b)
  (Inter.IsSmallL (toClass a) (toClass b) (SetIsSmall a)).

(* Notation "a :/\: b" := (inter a b)                                           *)
Global Instance SetAnd : And U := { and := inter }.

(* Characterisation of the elements of the intersection of two sets.            *)
Proposition InterCharac : forall (a b:U),
 forall x, x :< a:/\:b <-> x :< a /\ x :< b.
Proof.
  intros a b x. split; intros H1.
  - apply FromClassCharac in H1. apply H1.
  - apply FromClassCharac, H1.
Qed.

(* The intersection of two sets is commutative.                                 *)
Proposition InterComm : forall (a b:U), a:/\:b = b:/\:a.
Proof.
  intros a b. apply Extensionality. intros x. split;
  intros H1; apply InterCharac; apply InterCharac in H1;
  destruct H1 as [H1 H2]; auto.
Qed.

(* The intersection of two sets is associative.                                 *)
Proposition InterAssoc : forall (a b c:U), (a:/\:b):/\:c = a:/\:(b:/\:c).
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1;
  apply InterCharac in H1; apply InterCharac; destruct H1 as [H1 H2]; split.
  - apply InterCharac in H1. destruct H1 as [H1 _]. apply H1.
  - apply InterCharac in H1. destruct H1 as [_ H1]. apply InterCharac. auto.
  - apply InterCharac in H2. destruct H2 as [H2 _]. apply InterCharac. auto.
  - apply InterCharac in H2. destruct H2 as [_ H2]. apply H2.
Qed.

(* The intersection is distributive over the union.                             *)
Proposition InterDistOverUnion : forall (a b c:U),
  a:/\:(b:\/:c) = (a:/\:b):\/:(a:/\:c).
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1.
  - apply InterCharac in H1. destruct H1 as [H1 H2].
    apply Union2Charac in H2. destruct H2 as [H2|H2]; apply Union2Charac.
    + left.  apply InterCharac. auto.
    + right. apply InterCharac. auto.
  - apply Union2Charac in H1. destruct H1 as [H1|H1];
    apply InterCharac; split; apply InterCharac in H1.
    + destruct H1 as [H1 _]. apply H1.
    + destruct H1 as [_ H1]. apply Union2Charac. left. apply H1.
    + destruct H1 as [H1 _]. apply H1.
    + destruct H1 as [_ H1]. apply Union2Charac. right. apply H1.
Qed.

(* The union is distributive over the intersection                              *)
Proposition UnionDistOverInter : forall (a b c:U),
  a:\/:(b:/\:c) = (a:\/:b):/\:(a:\/:c).
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1.
  - apply Union2Charac in H1. destruct H1 as [H1|H1];
    apply InterCharac; split; apply Union2Charac.
    + left. apply H1.
    + left. apply H1.
    + right. apply InterCharac in H1. destruct H1 as [H1 _]. apply H1.
    + right. apply InterCharac in H1. destruct H1 as [_ H1]. apply H1.
  - apply InterCharac in H1. destruct H1 as [H1 H2]. apply Union2Charac.
    apply Union2Charac in H1. apply Union2Charac in H2.
    destruct H1 as [H1|H1]; destruct H2 as [H2|H2].
    + left. apply H1.
    + left. apply H1.
    + left. apply H2.
    + right. apply InterCharac. auto.
Qed.

Proposition NotInInter : forall (a b:U),
  forall x, ~ x :< a:/\:b -> ~ x :< a \/ ~ x :< b.
Proof.
  intros a b x H1.
  assert (x :< a \/ ~ x :< a) as H2. { apply LawExcludedMiddle. }
  destruct H2 as [H2|H2].
  - right. intros H3. apply H1. apply InterCharac. split; assumption.
  - left. apply H2.
Qed.

(* Intersection is compatible with inclusion.                                   *)
Proposition InterInclCompat : forall (a b c d:U),
  a :<=: b -> c :<=: d -> a:/\:c :<=: b:/\:d.
Proof.
  intros a b c d H1 H2 x H3. apply InterCharac in H3.
  destruct H3 as [H3 H4]. apply InterCharac. split.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

(* Intersection is left-compatible with inclusion.                              *)
Proposition InterInclCompatL : forall (a b c:U),
  a :<=: b -> a:/\:c :<=: b:/\:c.
Proof.
  intros a b c H1. apply InterInclCompat.
  - assumption.
  - apply InclRefl.
Qed.

(* Intersection is right-compatible with inclusion.                             *)
Proposition InterInclCompatR : forall (a b c:U),
  a :<=: b -> c:/\:a :<=: c:/\:b.
Proof.
  intros a b c H1. apply InterInclCompat.
  - apply InclRefl.
  - assumption.
Qed.

Proposition InterInclL : forall (a b:U), a:/\:b :<=: a.
Proof.
  intros a b x H1. apply InterCharac in H1. destruct H1 as [H1 _]. apply H1.
Qed.

Proposition InterInclR : forall (a b:U), a:/\:b :<=: b.
Proof.
  intros a b x H1. apply InterCharac in H1. destruct H1 as [_ H1]. apply H1.
Qed.

Proposition InterEqualIncl : forall (a b:U),
  a = a :/\: b <-> a :<=: b.
Proof.
  intros a b. split; intros H1.
  - intros x H2. rewrite H1 in H2. apply InterCharac in H2.
    destruct H2 as [_ H2]. apply H2.
  - apply Extensionality. intros x. split; intros H2.
    + apply InterCharac. split.
      * apply H2.
      * apply H1, H2.
    + apply InterCharac in H2. destruct H2 as [H2 _]. apply H2.
Qed.

