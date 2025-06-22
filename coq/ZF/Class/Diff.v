Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Complement.
Require Import ZF.Class.Core.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Complement.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Less.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Small.
Require Import ZF.Class.Union2.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

Require Import ZF.Notation.Diff.
Export ZF.Notation.Diff.

Definition diff (P Q:Class) : Class := P :/\: :¬:Q.

(* Notation "P :\: Q" := (diff P Q)                                             *)
Global Instance ClassDiff : Diff Class := { diff := diff }.

Proposition EquivCompat : forall (P Q R S:Class),
  P :~: R -> Q :~: S -> P :\: Q :~: R :\: S.
Proof.
  intros P Q R S H1 H2. apply Inter2.EquivCompat. 1: assumption.
  apply Complement.EquivCompat. assumption.
Qed.

Proposition IsSmall : forall (P Q:Class), Small P -> Small (P :\: Q).
Proof.
  intros P Q. apply Inter2.IsSmallL.
Qed.

Proposition WhenEmpty : forall (P Q:Class),
  P :\: Q  :~: :0: <-> P :<=: Q.
Proof.
  intros P Q. split; intros H1.
  - intros x H2. apply DoubleNegation. intros H3.
    apply Class.Empty.Charac with x, H1. split; assumption.
  - intros x. split; intros H2.
    + destruct H2 as [H2 H3].
      apply H1 in H2. contradiction.
    + apply Class.Empty.Charac in H2. contradiction.
Qed.

Proposition WhenNotEmpty : forall (P Q:Class),
  P :\: Q :<>: :0: -> P :<>: Q.
Proof.
  intros P Q H1 H2. apply Class.Empty.HasElem in H1.
  destruct H1 as [x [H1 H3]]. apply H3, H2. assumption.
Qed.

Proposition WhenLess : forall (P Q:Class),
  P :<: Q -> Q :\: P :<>: :0:.
Proof.
  intros P Q H1. apply HasElem.
  apply Less.Exists in H1. destruct H1 as [_ H1]. assumption.
Qed.

Proposition UnionInter : forall (P Q R:Class),
  P :\: (Q:\/:R) :~: (P:\:Q) :/\: P:\:R.
Proof.
  intros P Q R x. split; intros H1.
  - destruct H1 as [H1 H2]. split; split.
    + assumption.
    + intros H3. apply H2. left. assumption.
    + assumption.
    + intros H3. apply H2. right. assumption.
  - destruct H1 as [H1 H2]. destruct H1 as [H1 H3]. destruct H2 as [_ H2]. split.
    + assumption.
    + intros H4. destruct H4 as [H4|H4]; contradiction.
Qed.

Proposition Image : forall (F A B:Class),
  Functional F^:-1: -> F:[B:\:A]: :~: F:[B]: :\: F:[A]:.
Proof.
  intros F A B H1 y. split; intros H2.
  - destruct H2 as [x [H2 H3]]. destruct H2 as [H2 H4]. split.
    + exists x. split; assumption.
    + intros [x' [H5 H6]]. assert (x' = x) as H7. {
        apply Converse.WhenFunctional with F y; assumption. }
      subst. contradiction.
  - destruct H2 as [[x [H2 H3]] H4].
    exists x. split. 2: assumption. split.
    1: assumption. intros H5. apply H4. exists x. split; assumption.
Qed.

