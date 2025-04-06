Require Import ZF.Class.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Small.
Require Import ZF.Class.Specification.
Require Import ZF.Set.

Require Import ZF.Core.And.
Export ZF.Core.And.

(* The intersection of two classes P and Q.                                     *)
Definition inter (P Q:Class) : Class := fun x => P x /\ Q x.

(* Notation "P :/\: Q" := (inter P Q)                                           *)
Global Instance ClassAnd : And Class := { and := inter }.

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
  - apply Class.EquivRefl.
Qed.

Proposition EquivCompatR : forall (P Q R:Class),
  P :~: Q -> R :/\: P :~: R :/\: Q.
Proof.
  intros P Q R H1. apply EquivCompat.
  - apply Class.EquivRefl.
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
  - apply InclRefl.
Qed.

Proposition InclCompatR : forall (P Q R:Class),
  P :<=: Q -> R :/\: P :<=: R :/\: Q.
Proof.
  intros P Q R H1. apply InclCompat.
  - apply InclRefl.
  - assumption.
Qed.

Proposition Comm : forall (P Q:Class),
  P :/\: Q :~: Q :/\: P.
Proof.
  intros P Q x. split; intros H1;
  destruct H1 as [H1 H2]; split; assumption.
Qed.

Proposition InclL : forall (P Q:Class),
  P :/\: Q :<=: P.
Proof.
  intros P Q x H1. apply H1.
Qed.

Proposition InclR : forall (P Q:Class),
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
  assert (exists a, toClass a :~: P) as H2. { apply (proj1 (SmallIsSomeSet _)), H1. }

  (* So let a be a set equivalent to the class P. *)
  destruct H2 as [a H2].

  (* We need to show that the intersection of P and Q is small. *)
  assert (Small (P :/\: Q)) as A. 2: apply A.

  (* The property of being small being compatible with equivalences... *)
  apply SmallEquivCompat with (toClass a :/\: Q).

  (* We first need to show the equivalence between a /\ Q and P /\ Q. *)
  - assert (toClass a :/\: Q :~: P :/\: Q) as A. 2: apply A.

  (* Which follows from the equivalence between a and P. *)
    apply EquivCompatL, H2.

  (* We next need to show that a /\ Q is small. *)
  - assert (Small (toClass a :/\: Q)) as A. 2: apply A.

  (* Which follows from the spefication axiom (theorem). *)
    apply Specification.
Qed.

Proposition IsSmallR : forall (P Q:Class),
  Small Q -> Small (P:/\:Q).
Proof.
  intros P Q H1. apply SmallEquivCompat with (Q :/\: P).
  - apply Comm.
  - apply IsSmallL. assumption.
Qed.

Proposition InclInter : forall (P Q R:Class),
  R :<=: P -> R :<=: Q -> R :<=: P :/\: Q.
Proof.
  intros P Q R H1 H2 x H3. split.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

Proposition IsInterInclL : forall (P Q:Class),
  P :~: P :/\: Q <-> P :<=: Q.
Proof.
  intros P Q. split; intros H1.
  - apply Incl.EquivCompatL with (P:/\:Q). 2: apply InclR. apply EquivSym. assumption.
  - apply DoubleInclusion. split.
    + apply InclInter. 2: assumption. apply InclRefl.
    + apply InclL.
Qed.

Proposition IsInterInclR : forall (P Q:Class),
  Q :~: P :/\: Q <-> Q :<=: P.
Proof.
  intros P Q. split; intros H1.
  - apply Incl.EquivCompatL with (P:/\:Q). 2: apply InclL. apply EquivSym. assumption.
  - apply DoubleInclusion. split.
    + apply InclInter. 1: assumption. apply InclRefl.
    + apply InclR.
Qed.
