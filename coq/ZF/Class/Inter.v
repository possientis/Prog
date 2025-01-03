Require Import ZF.Axiom.Specification.
Require Import ZF.Class.
Require Import ZF.Class.Small.
Require Import ZF.Core.And.
Require Import ZF.Core.Equiv.
Require Import ZF.Set.

(* The intersection of two classes P and Q.                                     *)
Definition inter (P Q:Class) : Class := fun x => P x /\ Q x.

(* Notation "P :/\: Q" := (inter P Q)                                           *)
Global Instance ClassAnd : And Class := { and := inter }.

Proposition InterCharac : forall (P Q:Class) (x:U),
  (P:/\:Q) x <-> P x /\ Q x.
Proof.
  intros P Q x. split; intros H1; apply H1.
Qed.

Proposition InterEquivCompat : forall (P Q R S:Class),
  P :~: Q -> R :~: S -> P :/\: R :~: Q :/\: S.
Proof.
  intros P Q R S H1 H2 x. split; intros H3;
  apply (proj1 (InterCharac _ _ _)) in H3; destruct H3 as [H3 H4];
  apply InterCharac; split.
  - apply H1. assumption.
  - apply H2. assumption.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

Proposition InterEquivCompatL : forall (P Q R:Class),
  P :~: Q -> P :/\: R :~: Q :/\: R.
Proof.
  intros P Q R H1. apply InterEquivCompat.
  - assumption.
  - apply ClassEquivRefl.
Qed.

Proposition InterEquivCompatR : forall (P Q R:Class),
  P :~: Q -> R :/\: P :~: R :/\: Q.
Proof.
  intros P Q R H1. apply InterEquivCompat.
  - apply ClassEquivRefl.
  - assumption.
Qed.

Proposition InterComm : forall (P Q:Class),
  P :/\: Q :~: Q :/\: P.
Proof.
  intros P Q x. split; intros H1;
  apply (proj1 (InterCharac _ _ _)) in H1; destruct H1 as [H1 H2];
  apply InterCharac; split; assumption.
Qed.

Proposition InterIsSmallL : forall (P Q:Class),
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
    apply InterEquivCompatL, H2.

  (* We next need to show that a /\ Q is small. *)
  - assert (Small (toClass a :/\: Q)) as A. 2: apply A.

  (* Which follows from the spefication axiom (theorem). *)
    apply Specification.
Qed.

Proposition InterIsSmallR : forall (P Q:Class),
  Small Q -> Small (P:/\:Q).
Proof.
  intros P Q H1. apply SmallEquivCompat with (Q :/\: P).
  - apply InterComm.
  - apply InterIsSmallL. assumption.
Qed.
