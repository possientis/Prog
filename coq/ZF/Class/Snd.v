Require Import ZF.Class.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Image.
Require Import ZF.Class.Range.
Require Import ZF.Core.Equal.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Snd is the class of ordered pairs of the form ((y,z),z).                     *)
Definition Snd : Class := fun x =>
  exists y, exists z, x = :(:(y,z):,z):.

Proposition SndCharac2 : forall (x x':U),
  Snd :(x,x'): <-> exists y, exists z, x = :(y,z): /\ x' = z.
Proof.
  intros x x'. split; intros H1.
  - unfold Snd in H1. destruct H1 as [y [z H1]]. apply OrdPairEqual in H1.
    exists y. exists z. assumption.
  - destruct H1 as [y [z [H1 H2]]]. unfold Snd. exists y. exists z.
    rewrite H1, H2. reflexivity.
Qed.

Proposition SndIsFunctional : Functional Snd.
Proof.
  apply FunctionalCharac. intros x x1 x2 H1 H2.
  apply SndCharac2 in H1. apply SndCharac2 in H2.
  destruct H1 as [y1 [z1 [H1 G1]]]. destruct H2 as [y2 [z2 [H2 G2]]].
  subst. apply OrdPairEqual in H2. destruct H2 as [H1 H2]. subst. reflexivity.
Qed.

(* The direct image of a class P by Snd is the range of P.                      *)
Proposition ImageBySnd : forall (P:Class),
  Snd :[P]: :~: range P.
Proof.
  intros P x. split; intros H1.
  - unfold image in H1. destruct H1 as [x' [H1 H2]]. apply SndCharac2 in H2.
    destruct H2 as [y [z [H2 H3]]]. apply RangeCharac. exists y.
    subst. assumption.
  - apply (proj1 (RangeCharac _ _)) in H1. destruct H1 as [z H1].
    unfold image. exists :(z,x):. split.
    + assumption.
    + apply SndCharac2. exists z. exists x. split; reflexivity.
Qed.
