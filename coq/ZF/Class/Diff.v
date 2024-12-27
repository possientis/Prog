Require Import ZF.Class.
Require Import ZF.Class.Complement.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Small.
Require Import ZF.Class.Union.
Require Import ZF.Core.And.
Require Import ZF.Core.Diff.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Or.
Require Import ZF.Core.Not.
Require Import ZF.Set.

Definition diff (P Q:Class) : Class := P :/\: :¬:Q.

(* Notation "P :\: Q" := (diff P Q)                                             *)
Global Instance ClassDiff : Diff Class := { diff := diff }.

Proposition DiffCharac : forall (P Q:Class) (x:U),
  (P :\: Q) x <-> P x /\ ~ (Q x).
Proof.
  intros P Q x. split; intros H1; apply H1.
Qed.

Proposition DiffIsSmall : forall (P Q:Class), Small P -> Small (P :\: Q).
Proof.
  intros P Q. apply InterIsSmallL.
Qed.

Proposition DiffUnionInter : forall (P Q R:Class),
  P :\: (Q:\/:R) :~: (P:\:Q) :/\: P:\:R.
Proof.
  intros P Q R x. split; intros H1.
  - apply DiffCharac in H1. destruct H1 as [H1 H2]. apply InterCharac.
    apply (proj1 (ComplementCharac _ _)) in H2.
    split; apply DiffCharac; split.
    + assumption.
    + intros H3. apply H2. apply UnionCharac. left. assumption.
    + assumption.
    + intros H3. apply H2. apply UnionCharac. right. assumption.
  - apply InterCharac in H1. destruct H1 as [H1 H2].
    apply DiffCharac in H1. destruct H1 as [H1 H3].
    apply (proj1 (ComplementCharac _ _)) in H3.
    apply DiffCharac in H2. destruct H2 as [_ H2].
    apply (proj1 (ComplementCharac _ _)) in H2.
    apply DiffCharac. split.
    + assumption.
    + intros H4. apply (proj1 (UnionCharac _ _ _)) in H4.
      destruct H4 as [H4|H4]; contradiction.
Qed.
