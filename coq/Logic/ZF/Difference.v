Declare Scope ZF_Difference_scope.
Open    Scope ZF_Difference_scope.

Require Import Logic.ZF.Classic.
Require Import Logic.ZF.Core.
Require Import Logic.ZF.Empty.
Require Import Logic.ZF.Extensionality.
Require Import Logic.ZF.Intersect.
Require Import Logic.ZF.Specification.
Require Import Logic.ZF.Union.

(* The set a \ b is made of those elements of a which do not belong to b.       *)
Definition difference (a b:U) : U := :{a | fun x => ~ x :< b }:.

Notation "a :\: b" := (difference a b)
  (at level 3, no associativity) : ZF_Difference_scope.

Proposition DiffCharac : forall (a b:U),
  forall x, x :< a:\:b <-> x :< a /\ ~ x :< b.
Proof.
  intros a b x. unfold difference. apply SpecCharac.
Qed.

Proposition DiffUnionIntersect : forall (a b c:U),
  a :\: (b:\/:c) = a:\:b :/\: a:\:c.
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1.
  - apply DiffCharac in H1. destruct H1 as [H1 H2]. apply IntersectCharac.
    split; apply DiffCharac; split.
    + apply H1.
    + intros H3. apply H2. apply UnionCharac. left. apply H3.
    + apply H1.
    + intros H3. apply H2. apply UnionCharac. right. apply H3.
  - apply IntersectCharac in H1. destruct H1 as [H1 H2].
    apply DiffCharac in H1. destruct H1 as [H1 H3].
    apply DiffCharac in H2. destruct H2 as [_  H2].
    apply DiffCharac. split.
    + apply H1.
    + intros H4. apply UnionCharac in H4. destruct H4 as [H4|H4]; contradiction.
Qed.

Proposition DiffIntersectUnion : forall (a b c:U),
  a :\: (b:/\:c) = a:\:b :\/: a:\:c.
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1.
  - apply DiffCharac in H1. destruct H1 as [H1 H2].
    apply UnionCharac. apply NotInIntersect in H2. destruct H2 as [H2|H2].
    + left.  apply DiffCharac. split; assumption.
    + right. apply DiffCharac. split; assumption.
  - apply UnionCharac in H1. destruct H1 as [H1|H1];
    apply DiffCharac; split; apply DiffCharac in H1; destruct H1 as [H1 H2].
    + apply H1.
    + intros H3. apply IntersectCharac in H3. destruct H3 as [H3 _]. contradiction.
    + apply H1.
    + intros H3. apply IntersectCharac in H3. destruct H3 as [_ H3]. contradiction.
Qed.

Proposition DiffDiff : forall (a b:U),
  a :\: (b :\: a) = a.
Proof.
  intros a b. apply Extensionality. intros x. split; intros H1.
  - apply DiffCharac in H1. destruct H1 as [H1 _]. apply H1.
  - apply DiffCharac. split.
    + apply H1.
    + intros H2. apply DiffCharac in H2. destruct H2 as [_ H2]. contradiction.
Qed.

Proposition IntersectDistOverDiff : forall (a b c:U),
  a :/\: (b :\: c) = (a:/\:b) :\: (a:/\:c).
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1.
  - apply IntersectCharac in H1. destruct H1 as [H1 H2].
    apply DiffCharac in H2. destruct H2 as [H2 H3].
    apply DiffCharac. split.
    + apply IntersectCharac. split; assumption.
    + intros H4. apply IntersectCharac in H4. destruct H4 as [_ H4]. contradiction.
  - apply DiffCharac in H1. destruct H1 as [H1 H2].
    apply IntersectCharac in H1. destruct H1 as [H1 H3].
    apply NotInIntersect in H2. destruct H2 as [H2|H2]; apply IntersectCharac; split.
    + apply H1.
    + contradiction.
    + apply H1.
    + apply DiffCharac. split; assumption.
Qed.

Proposition IntersectDiffAssoc : forall (a b c:U),
  a :/\: (b :\: c) = (a :/\: b) :\: c.
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1.
  - apply IntersectCharac in H1. destruct H1 as [H1 H2].
    apply DiffCharac in H2. destruct H2 as [H2 H3].
    apply DiffCharac. split.
    + apply IntersectCharac. split; assumption.
    + apply H3.
  - apply DiffCharac in H1. destruct H1 as [H1 H2].
    apply IntersectCharac in H1. destruct H1 as [H1 H3].
    apply IntersectCharac. split.
    + apply H1.
    + apply DiffCharac. split; assumption.
Qed.


