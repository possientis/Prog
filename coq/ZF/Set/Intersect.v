Require Import ZF.Axiom.Classic.
Require Import ZF.Axiom.Extensionality.
Require Import ZF.Core.And.
Require Import ZF.Core.Leq.
Require Import ZF.Core.Or.
Require Import ZF.Set.
Require Import ZF.Set.Include.
Require Import ZF.Set.Specify.
Require Import ZF.Set.Union.

(* The intersection of two sets a and b.                                        *)
Definition intersect (a b:U) : U := :{ a | fun x => x :< b }:.

(* Notation "a :/\: b" := (intersect a b)                                       *)
Global Instance SetAnd : And U := { and := intersect }.

(* Characterisation of the elements of the intersection of two sets.            *)
Proposition IntersectCharac : forall (a b:U),
 forall x, x :< a:/\:b <-> x :< a /\ x :< b.
Proof.
  intros a b x. unfold intersect. split.
  - intros H. apply SpecCharac in H. apply H.
  - intros [H1 H2]. apply SpecCharac. auto.
Qed.

(* The interection of two sets is commutative.                                  *)
Proposition IntersectComm : forall (a b:U), a:/\:b = b:/\:a.
Proof.
  intros a b. apply Extensionality. intros x. split;
  intros H1; apply IntersectCharac; apply IntersectCharac in H1;
  destruct H1 as [H1 H2]; auto.
Qed.

(* The intersection of two sets is associative.                                 *)
Proposition IntersectAssoc : forall (a b c:U), (a:/\:b):/\:c = a:/\:(b:/\:c).
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1;
  apply IntersectCharac in H1; apply IntersectCharac; destruct H1 as [H1 H2]; split.
  - apply IntersectCharac in H1. destruct H1 as [H1 _]. apply H1.
  - apply IntersectCharac in H1. destruct H1 as [_ H1]. apply IntersectCharac. auto.
  - apply IntersectCharac in H2. destruct H2 as [H2 _]. apply IntersectCharac. auto.
  - apply IntersectCharac in H2. destruct H2 as [_ H2]. apply H2.
Qed.

(* The intersection is distributive over the union.                             *)
Proposition IntersectDistOverUnion : forall (a b c:U),
  a:/\:(b:\/:c) = (a:/\:b):\/:(a:/\:c).
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1.
  - apply IntersectCharac in H1. destruct H1 as [H1 H2].
    apply UnionCharac in H2. destruct H2 as [H2|H2]; apply UnionCharac.
    + left.  apply IntersectCharac. auto.
    + right. apply IntersectCharac. auto.
  - apply UnionCharac in H1. destruct H1 as [H1|H1];
    apply IntersectCharac; split; apply IntersectCharac in H1.
    + destruct H1 as [H1 _]. apply H1.
    + destruct H1 as [_ H1]. apply UnionCharac. left. apply H1.
    + destruct H1 as [H1 _]. apply H1.
    + destruct H1 as [_ H1]. apply UnionCharac. right. apply H1.
Qed.

(* The union is distributive over the intersection                              *)
Proposition UnionDistOverIntersect : forall (a b c:U),
  a:\/:(b:/\:c) = (a:\/:b):/\:(a:\/:c).
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1.
  - apply UnionCharac in H1. destruct H1 as [H1|H1];
    apply IntersectCharac; split; apply UnionCharac.
    + left. apply H1.
    + left. apply H1.
    + right. apply IntersectCharac in H1. destruct H1 as [H1 _]. apply H1.
    + right. apply IntersectCharac in H1. destruct H1 as [_ H1]. apply H1.
  - apply IntersectCharac in H1. destruct H1 as [H1 H2]. apply UnionCharac.
    apply UnionCharac in H1. apply UnionCharac in H2.
    destruct H1 as [H1|H1]; destruct H2 as [H2|H2].
    + left. apply H1.
    + left. apply H1.
    + left. apply H2.
    + right. apply IntersectCharac. auto.
Qed.

Proposition NotInIntersect : forall (a b:U),
  forall x, ~ x :< a:/\:b -> ~ x :< a \/ ~ x :< b.
Proof.
  intros a b x H1.
  assert (x :< a \/ ~ x :< a) as H2. { apply LawExcludedMiddle. }
  destruct H2 as [H2|H2].
  - right. intros H3. apply H1. apply IntersectCharac. split; assumption.
  - left. apply H2.
Qed.

(* Intersection is compatible with inclusion.                                   *)
Proposition IntersectInclCompat : forall (a b c d:U),
  a :<=: b -> c :<=: d -> a:/\:c :<=: b:/\:d.
Proof.
  intros a b c d H1 H2 x H3. apply IntersectCharac in H3.
  destruct H3 as [H3 H4]. apply IntersectCharac. split.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

(* Intersection is left-compatible with inclusion                               *)
Proposition IntersectInclCompatL : forall (a b c:U),
  a :<=: b -> a:/\:c :<=: b:/\:c.
Proof.
  intros a b c H1. apply IntersectInclCompat.
  - assumption.
  - apply InclRefl.
Qed.

(* Intersection is right-compatible with inclusion                              *)
Proposition IntersectInclCompatR : forall (a b c:U),
  a :<=: b -> c:/\:a :<=: c:/\:b.
Proof.
  intros a b c H1. apply IntersectInclCompat.
  - apply InclRefl.
  - assumption.
Qed.

Proposition IntersectInclL : forall (a b:U), a:/\:b :<=: a.
Proof.
  intros a b x H1. apply IntersectCharac in H1. destruct H1 as [H1 _]. apply H1.
Qed.

Proposition IntersectInclR : forall (a b:U), a:/\:b :<=: b.
Proof.
  intros a b x H1. apply IntersectCharac in H1. destruct H1 as [_ H1]. apply H1.
Qed.

Proposition IntersectEqualIncl : forall (a b:U),
  a = a :/\: b <-> a :<=: b.
Proof.
  intros a b. split; intros H1.
  - intros x H2. rewrite H1 in H2. apply IntersectCharac in H2.
    destruct H2 as [_ H2]. apply H2.
  - apply Extensionality. intros x. split; intros H2.
    + apply IntersectCharac. split.
      * apply H2.
      * apply H1, H2.
    + apply IntersectCharac in H2. destruct H2 as [H2 _]. apply H2.
Qed.


