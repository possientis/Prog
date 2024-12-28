Require Import ZF.Class.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Small.
Require Import ZF.Core.And.
Require Import ZF.Core.Prod.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter.
Require Import ZF.Set.OrdPair.

(* We consider the set defined by the product predicate of the sets a and b     *)
Definition prod (a b:U) : U := fromClass (toClass a :x: toClass b)
  (ProdIsSmall (toClass a) (toClass b) (SetIsSmall a) (SetIsSmall b)).

(* Notation "a :x: b" := (prod a b)                                             *)
Global Instance SetProd : Prod U := { prod := prod }.

(* Characterisation of the elements of the product axb *)
Proposition ProdCharac : forall (a b:U),
  forall x, x :< a :x: b <-> exists y, exists z, x = :(y,z): /\ y :< a /\ z :< b.
Proof.
  intros a b x. unfold Core.Prod.prod, SetProd, prod. split; intros H1.
  - apply FromClassCharac in H1.
    apply (proj1 (Class.Prod.ProdCharac _ _ _)) in H1. apply H1.
  - apply FromClassCharac, Class.Prod.ProdCharac, H1.
Qed.

Proposition ProdCharac2 : forall (a b:U),
  forall y, forall z, :(y,z): :< a :x: b <-> y :< a /\ z :< b.
Proof.
  intros a b y z. split; intros H1.
  - apply ProdCharac in H1. destruct H1 as [y' [z' [H1 [Hya Hzb]]]].
    apply OrdPairEqual in H1. destruct H1 as [H1 H2]. subst. split; assumption.
  - destruct H1 as [Hya Hzb]. apply ProdCharac. exists y. exists z. split.
    + reflexivity.
    + split; assumption.
Qed.

Proposition InterProdIsProdInter: forall (a1 a2 b1 b2:U),
  (a1:x:b1) :/\: (a2:x:b2) = (a1:/\:a2) :x: (b1:/\:b2).
Proof.
  intros a1 a2 b1 b2. apply DoubleInclusion. split; intros x H1.
  - apply InterCharac in H1. destruct H1 as [H1 H2].
    apply ProdCharac in H1. destruct H1 as [y1 [z1 [G1 [H1 H1']]]].
    apply ProdCharac in H2. destruct H2 as [y2 [z2 [G2 [H2 H2']]]].
    subst. apply OrdPairEqual in G2. destruct G2 as [G1 G2]. subst.
    apply ProdCharac2. split; apply InterCharac; split; assumption.
  - apply ProdCharac in H1. destruct H1 as [y [z [H1 [Ha Hb]]]].
    apply InterCharac in Ha. destruct Ha as [Ha Ha'].
    apply InterCharac in Hb. destruct Hb as [Hb Hb'].
    apply InterCharac. split; apply ProdCharac; exists y; exists z; split.
    + assumption.
    + split; assumption.
    + assumption.
    + split; assumption.
Qed.
