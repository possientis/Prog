Require Import ZF.Axiom.Classic.
Require Import ZF.Axiom.Extensionality.
Require Import ZF.Class.Core.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter.
Require Import ZF.Set.Union2.
Export ZF.Notation.Diff.

Definition diff (a b:U) : U := fromClass (toClass a :\: toClass b)
  (Diff.IsSmall (toClass a) (toClass b) (SetIsSmall a)).

(* Notation "a :\: b" := (diff a b)                                             *)
Global Instance SetDiff : Diff U := { diff := diff }.

(* The set a \ b is made of those elements of a which do not belong to b.       *)
Proposition Charac : forall (a b:U),
  forall x, x :< a:\:b <-> x :< a /\ ~ x :< b.
Proof.
  intros a b x. split; intros H1.
  - apply FromClass.Charac in H1. apply H1.
  - apply FromClass.Charac, H1.
Qed.

Proposition DiffOfUnion : forall (a b c:U), a :\: (b:\/:c) = a:\:b :/\: a:\:c.
Proof.
intros a b c. apply Extensionality. intros x. split; intros H1.
  - apply Diff.Charac in H1. destruct H1 as [H1 H2]. apply InterCharac.
    split; apply Diff.Charac; split.
    + apply H1.
    + intros H3. apply H2. apply Union2Charac. left. apply H3.
    + apply H1.
    + intros H3. apply H2. apply Union2Charac. right. apply H3.
  - apply InterCharac in H1. destruct H1 as [H1 H2].
    apply Diff.Charac in H1. destruct H1 as [H1 H3].
    apply Diff.Charac in H2. destruct H2 as [_  H2].
    apply Diff.Charac. split.
    + apply H1.
    + intros H4. apply Union2Charac in H4. destruct H4 as [H4|H4]; contradiction.
Qed.

Proposition DiffOfInter : forall (a b c:U),
  a :\: (b:/\:c) = a:\:b :\/: a:\:c.
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1.
  - apply Diff.Charac in H1. destruct H1 as [H1 H2].
    apply Union2Charac. apply NotInInter in H2. destruct H2 as [H2|H2].
    + left.  apply Diff.Charac. split; assumption.
    + right. apply Diff.Charac. split; assumption.
  - apply Union2Charac in H1. destruct H1 as [H1|H1];
    apply Diff.Charac; split; apply Diff.Charac in H1; destruct H1 as [H1 H2].
    + apply H1.
    + intros H3. apply InterCharac in H3. destruct H3 as [H3 _]. contradiction.
    + apply H1.
    + intros H3. apply InterCharac in H3. destruct H3 as [_ H3]. contradiction.
Qed.

Proposition DiffOfDiff : forall (a b:U),
  a :\: (b :\: a) = a.
Proof.
  intros a b. apply Extensionality. intros x. split; intros H1.
  - apply Diff.Charac in H1. destruct H1 as [H1 _]. apply H1.
  - apply Diff.Charac. split.
    + apply H1.
    + intros H2. apply Diff.Charac in H2. destruct H2 as [_ H2]. contradiction.
Qed.

Proposition InterDistOverDiff : forall (a b c:U),
  a :/\: (b :\: c) = (a:/\:b) :\: (a:/\:c).
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1.
  - apply InterCharac in H1. destruct H1 as [H1 H2].
    apply Diff.Charac in H2. destruct H2 as [H2 H3].
    apply Diff.Charac. split.
    + apply InterCharac. split; assumption.
    + intros H4. apply InterCharac in H4. destruct H4 as [_ H4]. contradiction.
  - apply Diff.Charac in H1. destruct H1 as [H1 H2].
    apply InterCharac in H1. destruct H1 as [H1 H3].
    apply NotInInter in H2. destruct H2 as [H2|H2]; apply InterCharac; split.
    + apply H1.
    + contradiction.
    + apply H1.
    + apply Diff.Charac. split; assumption.
Qed.

Proposition InterDiffAssoc : forall (a b c:U),
  a :/\: (b :\: c) = (a :/\: b) :\: c.
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1.
  - apply InterCharac in H1. destruct H1 as [H1 H2].
    apply Diff.Charac in H2. destruct H2 as [H2 H3].
    apply Diff.Charac. split.
    + apply InterCharac. split; assumption.
    + apply H3.
  - apply Diff.Charac in H1. destruct H1 as [H1 H2].
    apply InterCharac in H1. destruct H1 as [H1 H3].
    apply InterCharac. split.
    + apply H1.
    + apply Diff.Charac. split; assumption.
Qed.

Proposition WhenEmpty : forall (a b:U),
  a :\: b = :0: <-> a :<=: b.
Proof.
  intros a b. split; intros H1.
  - intros x Ha. apply DoubleNegation. intros Hb.
    assert (x :< :0:) as H2.
      { rewrite <- H1. apply Diff.Charac. split; assumption. }
    apply EmptyCharac in H2. contradiction.
  - apply Extensionality. intros x. split; intros H2.
    + apply Diff.Charac in H2. destruct H2 as [H2 H3].
      apply H1 in H2. contradiction.
    + apply EmptyCharac in H2. contradiction.
Qed.

Proposition IsIncl : forall (a b:U),
  a :\: b :<=: a.
Proof.
  intros a b x H1. apply Diff.Charac in H1. destruct H1 as [H1 _]. apply H1.
Qed.

(* Diff is 'compatible' with inclusion. Not quite of course.                    *)
Proposition InclCompat : forall (a b c d:U),
  a :<=: b -> c :<=: d -> a:\:d :<=: b:\:c.
Proof.
  intros a b c d H1 H2 x H3. apply Diff.Charac in H3.
  destruct H3 as [H3 H4]. apply Diff.Charac. split.
  - apply H1. assumption.
  - intros H5. apply H4, H2. assumption.
Qed.

(* Diff is left-compatible with inclusion.                                      *)
Proposition InclCompatL : forall (a b c:U),
  a :<=: b -> a :\: c :<=: b :\: c.
Proof.
  intros a b c H1. apply InclCompat.
  - assumption.
  - apply InclRefl.
Qed.

(* Diff is 'right-compatible' with inclusion. Not quite of course.              *)
Proposition InclCompatR : forall (a b c:U),
  a :<=: b -> c :\: b :<=: c :\: a.
Proof.
  intros a b c H1. apply InclCompat.
  - apply InclRefl.
  - assumption.
Qed.

