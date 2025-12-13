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

Proposition Charac2 : forall (a b y z:U),
  :(y,z): :< a :x: b <-> y :< a /\ z :< b.
Proof.
  intros a b y z. split; intros H1.
  - apply Charac in H1. destruct H1 as [y' [z' [H1 [Hya Hzb]]]].
    apply WhenEqual in H1. destruct H1 as [H1 H2]. subst. split; assumption.
  - destruct H1 as [Hya Hzb]. apply Charac. exists y. exists z. split.
    + reflexivity.
    + split; assumption.
Qed.

(* The product of two sets is compatible with inclusion.                        *)
Proposition InclCompat : forall (a b c d:U),
  a :<=: b -> c :<=: d -> a :x: c :<=: b :x: d.
Proof.
  intros a b c d H1 H2 x H3. apply Charac in H3.
  destruct H3 as [y [z [H3 [H4 H5]]]]. apply Charac. exists y. exists z.
  split. 1: assumption. split.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

(* The product of two sets is left-compatible with inclusion.                   *)
Proposition InclCompatL : forall (a b c:U),
  a :<=: b -> a :x: c :<=: b :x: c.
Proof.
  intros a b c H1. apply InclCompat.
  - assumption.
  - apply Incl.Refl.
Qed.

(* The product of two sets is right-compatible with inclusion.                  *)
Proposition InclCompatR : forall (a b c:U),
  a :<=: b -> c :x: a :<=: c :x: b.
Proof.
  intros a b c H1. apply InclCompat.
  - apply Incl.Refl.
  - assumption.
Qed.

Proposition Inter2 : forall (a1 a2 b1 b2:U),
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

