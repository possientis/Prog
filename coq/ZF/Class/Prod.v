Require Import ZF.Class.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Core.And.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Prod.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

Definition prod (P Q:Class) : Class := fun x =>
  exists y, exists z, x = :(y,z): /\ P y /\ Q z.

(* Notation "P :x: Q" := (prod P Q)                                             *)
Global Instance ClassProd : Prod Class := { prod := prod }.

Proposition ProdCharac2 : forall (P Q:Class),
  forall y, forall z, (P:x:Q) :(y,z): <-> P y /\ Q z.
Proof.
  intros P Q y z. split; intros H1.
  - unfold prod in H1. destruct H1 as [y' [z' [H1 [H2 H3]]]].
    apply OrdPairEqual in H1. destruct H1 as [H1 H1']. subst. split; assumption.
  - destruct H1 as [H1 H2]. exists y. exists z. split.
    + reflexivity.
    + split; assumption.
Qed.

Proposition InterProdIsProdInter: forall (P1 P2 Q1 Q2:Class),
  (P1:x:Q1) :/\: (P2:x:Q2) :~: (P1:/\:P2) :x: (Q1:/\:Q2).
Proof.
  intros P1 P2 Q1 Q2. apply DoubleInclusion. split; intros x H1.
  - destruct H1 as [H1 H2].
    destruct H1 as [y1 [z1 [G1 [H1 H1']]]].
    destruct H2 as [y2 [z2 [G2 [H2 H2']]]].
    subst. apply OrdPairEqual in G2. destruct G2 as [G1 G2]. subst.
    apply ProdCharac2. split; split; assumption.
  - unfold prod in H1. destruct H1 as [y [z [H1 [[H2 H2'] [H3 H3']]]]].
    split; exists y; exists z; split.
    + apply H1.
    + split; assumption.
    + apply H1.
    + split; assumption.
Qed.
