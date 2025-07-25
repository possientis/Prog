Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Small.
Require Import ZF.Axiom.Specification.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

Require Import ZF.Notation.And.
Export ZF.Notation.And.

(* The intersection of two classes P and Q.                                     *)
Definition inter2 (P Q:Class) : Class := fun x => P x /\ Q x.

(* Notation "P :/\: Q" := (inter P Q)                                           *)
Global Instance ClassAnd : And Class := { and := inter2 }.

Proposition EquivCompat : forall (P Q R S:Class),
  P :~: Q -> R :~: S -> P :/\: R :~: Q :/\: S.
Proof.
  intros P Q R S H1 H2 x. split; intros H3; destruct H3 as [H3 H4]; split.
  - apply H1. assumption.
  - apply H2. assumption.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

Proposition EquivCompatL : forall (P Q R:Class),
  P :~: Q -> P :/\: R :~: Q :/\: R.
Proof.
  intros P Q R H1. apply EquivCompat.
  - assumption.
  - apply Equiv.Refl.
Qed.

Proposition EquivCompatR : forall (P Q R:Class),
  P :~: Q -> R :/\: P :~: R :/\: Q.
Proof.
  intros P Q R H1. apply EquivCompat.
  - apply Equiv.Refl.
  - assumption.
Qed.

Proposition InclCompat : forall (P Q R S:Class),
  P :<=: Q -> R :<=: S -> P :/\: R :<=: Q :/\: S.
Proof.
  intros P Q R S H1 H2 x H3.
  destruct H3 as [H3 H4]; split.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

Proposition InclCompatL : forall (P Q R:Class),
  P :<=: Q -> P :/\: R :<=: Q :/\: R.
Proof.
  intros P Q R H1. apply InclCompat.
  - assumption.
  - apply Incl.Refl.
Qed.

Proposition InclCompatR : forall (P Q R:Class),
  P :<=: Q -> R :/\: P :<=: R :/\: Q.
Proof.
  intros P Q R H1. apply InclCompat.
  - apply Incl.Refl.
  - assumption.
Qed.

Proposition Comm : forall (P Q:Class),
  P :/\: Q :~: Q :/\: P.
Proof.
  intros P Q x. split; intros H1;
  destruct H1 as [H1 H2]; split; assumption.
Qed.

Proposition IsInclL : forall (P Q:Class),
  P :/\: Q :<=: P.
Proof.
  intros P Q x H1. apply H1.
Qed.

Proposition IsInclR : forall (P Q:Class),
  P :/\: Q :<=: Q.
Proof.
  intros P Q x H1. apply H1.
Qed.

Proposition IsSmallL : forall (P Q:Class),
  Small P -> Small (P:/\:Q).
Proof.

  (* Let P and Q be an arbitrary classes *)
  intros P Q.

  (* We assume that P is small *)
  intros H1. assert (Small P) as A. { apply H1. } clear A.

  (* In particular P is equivalent to some set a. *)
  assert (exists a, P :~: toClass a) as H2. { apply Small.IsSomeSet, H1. }

  (* So let a be a set equivalent to the class P. *)
  destruct H2 as [a H2].

  (* We need to show that the intersection of P and Q is small. *)
  assert (Small (P :/\: Q)) as A. 2: apply A.

  (* The property of being small being compatible with equivalences... *)
  apply Small.EquivCompat with (toClass a :/\: Q).

  (* We first need to show the equivalence between a /\ Q and P /\ Q. *)
  - assert (toClass a :/\: Q :~: P :/\: Q) as A. 2: apply A.

  (* Which follows from the equivalence between a and P. *)
    apply EquivCompatL, Equiv.Sym, H2.

  (* We next need to show that a /\ Q is small. *)
  - assert (Small (toClass a :/\: Q)) as A. 2: apply A.

  (* Which follows from the spefication axiom (theorem). *)
    apply Specification.
Qed.

Proposition IsSmallR : forall (P Q:Class),
  Small Q -> Small (P:/\:Q).
Proof.
  intros P Q H1. apply Small.EquivCompat with (Q :/\: P).
  - apply Comm.
  - apply IsSmallL. assumption.
Qed.

Proposition IsIncl : forall (P Q R:Class),
  R :<=: P -> R :<=: Q -> R :<=: P :/\: Q.
Proof.
  intros P Q R H1 H2 x H3. split.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

Proposition WhenInclL : forall (P Q:Class),
  P :<=: Q <-> P :/\: Q :~: P.
Proof.
  intros P Q. split; intros H1.
  - apply DoubleInclusion. split.
    + apply IsInclL.
    + apply IsIncl. 2: assumption. apply Incl.Refl.
  - apply Incl.EquivCompatL with (P:/\:Q). 2: apply IsInclR. assumption.
Qed.

Proposition WhenInclR : forall (P Q:Class),
  Q :<=: P <-> P :/\: Q :~: Q.
Proof.
  intros P Q. split; intros H1.
  - apply DoubleInclusion. split.
    + apply IsInclR.
    + apply IsIncl. 1: assumption. apply Incl.Refl.
  - apply Incl.EquivCompatL with (P:/\:Q). 2: apply IsInclL. assumption.
Qed.

Proposition Image : forall (F P Q:Class),
  F:[P :/\: Q]: :<=: F:[P]: :/\: F:[Q]:.
Proof.
  intros F P Q y [x [[H1 H2] H3]]. split; exists x; split; assumption.
Qed.
