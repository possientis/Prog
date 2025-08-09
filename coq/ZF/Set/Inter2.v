Require Import ZF.Axiom.Classic.
Require Import ZF.Axiom.Extensionality.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Union2.
Export ZF.Notation.And.

(* The intersection of two sets a and b.                                        *)
Definition inter2 (a b:U) : U := fromClass (toClass a :/\: toClass b)
  (Inter2.IsSmallL (toClass a) (toClass b) (SetIsSmall a)).

(* Notation "a :/\: b" := (inter a b)                                           *)
Global Instance SetAnd : And U := { and := inter2 }.

(* Characterisation of the elements of the intersection of two sets.            *)
Proposition Charac : forall (a b:U),
 forall x, x :< a:/\:b <-> x :< a /\ x :< b.
Proof.
  intros a b x. split; intros H1.
  - apply FromClass.Charac in H1. apply H1.
  - apply FromClass.Charac, H1.
Qed.

(* Intersection is compatible with inclusion.                                   *)
Proposition InclCompat : forall (a b c d:U),
  a :<=: b -> c :<=: d -> a:/\:c :<=: b:/\:d.
Proof.
  intros a b c d H1 H2 x H3. apply Charac in H3.
  destruct H3 as [H3 H4]. apply Charac. split.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

(* Intersection is left-compatible with inclusion.                              *)
Proposition InclCompatL : forall (a b c:U),
  a :<=: b -> a:/\:c :<=: b:/\:c.
Proof.
  intros a b c H1. apply InclCompat.
  - assumption.
  - apply Incl.Refl.
Qed.

(* Intersection is right-compatible with inclusion.                             *)
Proposition InclCompatR : forall (a b c:U),
  a :<=: b -> c:/\:a :<=: c:/\:b.
Proof.
  intros a b c H1. apply InclCompat.
  - apply Incl.Refl.
  - assumption.
Qed.

(* The intersection of two sets is commutative.                                 *)
Proposition Comm : forall (a b:U), a:/\:b = b:/\:a.
Proof.
  intros a b. apply Extensionality. intros x. split;
  intros H1; apply Charac; apply Charac in H1;
  destruct H1 as [H1 H2]; auto.
Qed.

(* The intersection of two sets is associative.                                 *)
Proposition Assoc : forall (a b c:U), (a:/\:b) :/\: c = a :/\: (b:/\:c).
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1;
  apply Charac in H1; apply Charac; destruct H1 as [H1 H2]; split.
  - apply Charac in H1. destruct H1 as [H1 _]. apply H1.
  - apply Charac in H1. destruct H1 as [_ H1]. apply Charac. auto.
  - apply Charac in H2. destruct H2 as [H2 _]. apply Charac. auto.
  - apply Charac in H2. destruct H2 as [_ H2]. apply H2.
Qed.

(* The intersection is distributive over the union.                             *)
Proposition Inter2DistOverUnion2 : forall (a b c:U),
  a :/\: (b:\/:c) = (a:/\:b) :\/: (a:/\:c).
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1.
  - apply Charac in H1. destruct H1 as [H1 H2].
    apply Union2.Charac in H2. destruct H2 as [H2|H2]; apply Union2.Charac.
    + left.  apply Charac. auto.
    + right. apply Charac. auto.
  - apply Union2.Charac in H1. destruct H1 as [H1|H1];
    apply Charac; split; apply Charac in H1.
    + destruct H1 as [H1 _]. apply H1.
    + destruct H1 as [_ H1]. apply Union2.Charac. left. apply H1.
    + destruct H1 as [H1 _]. apply H1.
    + destruct H1 as [_ H1]. apply Union2.Charac. right. apply H1.
Qed.

(* The union is distributive over the intersection                              *)
Proposition Union2DistOverInter2 : forall (a b c:U),
  a :\/: (b:/\:c) = (a:\/:b) :/\: (a:\/:c).
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1.
  - apply Union2.Charac in H1. destruct H1 as [H1|H1];
    apply Charac; split; apply Union2.Charac.
    + left. apply H1.
    + left. apply H1.
    + right. apply Charac in H1. destruct H1 as [H1 _]. apply H1.
    + right. apply Charac in H1. destruct H1 as [_ H1]. apply H1.
  - apply Charac in H1. destruct H1 as [H1 H2]. apply Union2.Charac.
    apply Union2.Charac in H1. apply Union2.Charac in H2.
    destruct H1 as [H1|H1]; destruct H2 as [H2|H2].
    + left. apply H1.
    + left. apply H1.
    + left. apply H2.
    + right. apply Charac. auto.
Qed.

Proposition WhenNotIn : forall (a b:U),
  forall x, ~ x :< a:/\:b -> ~ x :< a \/ ~ x :< b.
Proof.
  intros a b x H1.
  assert (x :< a \/ ~ x :< a) as H2. { apply LawExcludedMiddle. }
  destruct H2 as [H2|H2].
  - right. intros H3. apply H1. apply Charac. split; assumption.
  - left. apply H2.
Qed.

Proposition IsInclL : forall (a b:U), a:/\:b :<=: a.
Proof.
  intros a b x H1. apply Charac in H1. destruct H1 as [H1 _]. apply H1.
Qed.

Proposition IsInclR : forall (a b:U), a:/\:b :<=: b.
Proof.
  intros a b x H1. apply Charac in H1. destruct H1 as [_ H1]. apply H1.
Qed.

Proposition IsIncl : forall (a b c:U),
  c :<=: a -> c :<=: b -> c :<=: a :/\: b.
Proof.
  intros a b c H1 H2 x H3. apply Charac. split.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

Proposition WhenInclL : forall (a b:U),
  a :<=: b <-> a :/\: b = a.
Proof.
  intros a b. split; intros H1.
  - apply DoubleInclusion. split.
    + apply IsInclL.
    + apply IsIncl. 2: assumption. apply Incl.Refl.
  - rewrite <- H1. apply IsInclR.
Qed.

Proposition WhenInclR : forall (a b:U),
  b :<=: a <-> a :/\: b = b.
Proof.
  intros a b. split; intros H1.
  - apply DoubleInclusion. split.
    + apply IsInclR.
    + apply IsIncl. 1: assumption. apply Incl.Refl.
  - rewrite <- H1. apply IsInclL.
Qed.

Proposition Image : forall (f a b:U),
  f:[a :/\: b]: :<=: f:[a]: :/\: f:[b]:.
Proof.
  intros f a b y H1.
  apply Image.Charac in H1. destruct H1 as [x [H1 H2]].
  apply Charac in H1. destruct H1 as [H1 H3].
  apply Charac. split; apply Image.Charac; exists x; split; assumption.
Qed.

Proposition WhenEqualL : forall (a b:U),
  a = a :/\: b <-> a :<=: b.
Proof.
  intros a b. split; intros H1.
  - intros x H2. rewrite H1 in H2. apply Charac in H2.
    destruct H2 as [_ H2]. apply H2.
  - apply Extensionality. intros x. split; intros H2.
    + apply Charac. split.
      * apply H2.
      * apply H1, H2.
    + apply Charac in H2. destruct H2 as [H2 _]. apply H2.
Qed.

