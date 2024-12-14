Declare Scope ZF_Set_Intersect_scope.
Open    Scope ZF_Set_Intersect_scope.

Require Import ZF.Axiom.Classic.
Require Import ZF.Axiom.Extensionality.
Require Import ZF.Set.
Require Import ZF.Set.Specify.
Require Import ZF.Set.Union.

(* The intersection of two sets a and b.                                        *)
Definition intersect (a b:U) : U := :{ a | fun x => x :< b }:.

Notation "a :/\: b" := (intersect a b)
  (at level 11, right associativity) : ZF_Set_Intersect_scope.

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

