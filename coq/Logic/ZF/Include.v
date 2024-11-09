Declare Scope ZF_Include_scope.
Open    Scope ZF_Include_scope.

Require Import Logic.ZF.Core.
Require Import Logic.ZF.Extensionality.
Require Import Logic.ZF.Intersect.
Require Import Logic.ZF.Union.

(* Inclusion predicate between two sets.                                        *)
Definition Incl (a b:U) : Prop := forall x, x :< a -> x :< b.

Notation "a :<=: b" := (Incl a b)
  (at level 6, no associativity) : ZF_Include_scope.

(* Strict inclusion predicate.                                                  *)
Definition InclStrict (a b:U) : Prop := a :<=: b /\ ~a = b.

Notation "a :<: b" := (InclStrict a b)
  (at level 6, no associativity) : ZF_Include_scope.

(* Two sets are equal if and only if they are subsets of each other.            *)
Proposition DoubleInclusion : forall (a b:U),
  a = b <-> a :<=: b /\ b :<=: a.
Proof.
  intros a b. unfold Incl. split.
  - intros H1. split; intros x Hx.
    + rewrite <- H1. apply Hx.
    + rewrite H1. apply Hx.
  - intros [H1 H2]. apply Extensionality. intros x. split.
    + apply H1.
    + apply H2.
Qed.

(* The inclusion relation is reflexive.                                         *)
Proposition InclRefl : forall (a:U), a :<=: a.
Proof.
  intros a x. auto.
Qed.

(* The inclusion relation is anti-symmetric.                                    *)
Proposition InclAnti : forall (a b:U),
  a :<=: b -> b :<=: a -> a = b.
Proof.
  intros a b H1 H2. apply DoubleInclusion. split; assumption.
Qed.

(* The inclusion relation is transitive.                                        *)
Proposition InclTran : forall (a b c:U),
  a :<=: b -> b :<=: c -> a :<=: c.
Proof.
  intros a b c H1 H2 x H3. apply H2, H1, H3.
Qed.

(* The inclusion relation is left compatible with intersection.                 *)
Proposition InclCompatIntersectL : forall (a b c:U),
  a :<=: b -> c:/\:a :<=: c:/\:b.
Proof.
  intros a b c H1 x H2. apply IntersectCharac in H2. destruct H2 as [H2 H3].
  apply IntersectCharac. split.
  - apply H2.
  - apply H1, H3.
Qed.

(* The inclusion relation is right compatible with intersection.                 *)
Proposition InclCompatIntersectR : forall (a b c:U),
  a :<=: b -> a:/\:c :<=: b:/\:c.
Proof.
  intros a b c H1 x H2. apply IntersectCharac in H2. destruct H2 as [H2 H3].
  apply IntersectCharac. split.
  - apply H1, H2.
  - apply H3.
Qed.

(* The inclusion relation is left compatible with union.                        *)
Proposition InclCompatUnionL : forall (a b c:U),
  a :<=: b -> c:\/:a :<=: c:\/:b.
Proof.
  intros a b c H1 x H2. apply UnionCharac in H2. destruct H2 as [H2|H2];
  apply UnionCharac.
  - left. apply H2.
  - right. apply H1, H2.
Qed.

(* The inclusion relation is right compatible with union.                       *)
Proposition InclCompatUnionR : forall (a b c:U),
  a :<=: b -> a:\/:c :<=: b:\/:c.
Proof.
  intros a b c H1 x H2. apply UnionCharac in H2. destruct H2 as [H2|H2];
  apply UnionCharac.
  - left. apply H1, H2.
  - right. apply H2.
Qed.

Proposition InclEqualUnion : forall (a b:U),
  a :<=: b <-> b = a :\/: b.
Proof.
  intros a b. split; intros H1.
  - apply Extensionality. intros x. split; intros H2.
    + apply UnionCharac. right. apply H2.
    + apply UnionCharac in H2. destruct H2 as [H2|H2].
      * apply H1, H2.
      * apply H2.
  - intros x H2. rewrite H1. apply UnionCharac. left. apply H2.
Qed.

Proposition InclEqualIntersect : forall (a b:U),
  a :<=: b <-> a = a :/\: b.
Proof.
  intros a b. split; intros H1.
  - apply Extensionality. intros x. split; intros H2.
    + apply IntersectCharac. split.
      * apply H2.
      * apply H1, H2.
    + apply IntersectCharac in H2. destruct H2 as [H2 _]. apply H2.
  - intros x H2. rewrite H1 in H2. apply IntersectCharac in H2.
    destruct H2 as [_ H2]. apply H2.
Qed.

Proposition InclUnion1 : forall (a b:U), a :<=: a:\/:b.
Proof.
  intros a b x H1. apply UnionCharac. left. apply H1.
Qed.

Proposition InclUnion2 : forall (a b:U), b :<=: a:\/:b.
Proof.
  intros a b x H1. apply UnionCharac. right. apply H1.
Qed.

Proposition InclIntersect1 : forall (a b:U), a:/\:b :<=: a.
Proof.
  intros a b x H1. apply IntersectCharac in H1. destruct H1 as [H1 _]. apply H1.
Qed.

Proposition InclIntersect2 : forall (a b:U), a:/\:b :<=: b.
Proof.
  intros a b x H1. apply IntersectCharac in H1. destruct H1 as [_ H1]. apply H1.
Qed.

