Require Import ZF.Class.Equiv.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.OrdPair.
Export ZF.Notation.Prod.

(* We consider the set defined by the product predicate of the sets a and b     *)
Definition prod (a b:U) : U := fromClass (toClass a :x: toClass b)
  (IsSmall (toClass a) (toClass b) (SetIsSmall a) (SetIsSmall b)).

(* Notation "a :x: b" := (prod a b)                                             *)
Global Instance SetProd : Prod U := { prod := prod }.

(* Characterisation of the elements of the product axb *)
Proposition Charac : forall (a b:U),
  forall x, x :< a :x: b <-> exists y, exists z, x = :(y,z): /\ y :< a /\ z :< b.
Proof.
  intros a b x. split; intros H1.
  - apply FromClass.Charac in H1. assumption.
  - apply FromClass.Charac. assumption.
Qed.

Proposition Charac2 : forall (a b:U),
  forall y, forall z, :(y,z): :< a :x: b <-> y :< a /\ z :< b.
Proof.
  intros a b y z. split; intros H1.
  - apply Charac in H1. destruct H1 as [y' [z' [H1 [Hya Hzb]]]].
    apply WhenEqual in H1. destruct H1 as [H1 H2]. subst. split; assumption.
  - destruct H1 as [Hya Hzb]. apply Charac. exists y. exists z. split.
    + reflexivity.
    + split; assumption.
Qed.

Proposition InterProdIsProdInter: forall (a1 a2 b1 b2:U),
  (a1:x:b1) :/\: (a2:x:b2) = (a1:/\:a2) :x: (b1:/\:b2).
Proof.
  intros a1 a2 b1 b2. apply DoubleInclusion. split; intros x H1.
  - apply Inter2.Charac in H1. destruct H1 as [H1 H2].
    apply Charac in H1. destruct H1 as [y1 [z1 [G1 [H1 H1']]]].
    apply Charac in H2. destruct H2 as [y2 [z2 [G2 [H2 H2']]]].
    subst. apply WhenEqual in G2. destruct G2 as [G1 G2]. subst.
    apply Charac2. split; apply Inter2.Charac; split; assumption.
  - apply Charac in H1. destruct H1 as [y [z [H1 [Ha Hb]]]].
    apply Inter2.Charac in Ha. destruct Ha as [Ha Ha'].
    apply Inter2.Charac in Hb. destruct Hb as [Hb Hb'].
    apply Inter2.Charac. split; apply Charac; exists y; exists z; split.
    + assumption.
    + split; assumption.
    + assumption.
    + split; assumption.
Qed.
