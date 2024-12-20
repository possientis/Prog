Require Import ZF.Class.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Image.
Require Import ZF.Core.Equiv.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Switch is the class of ordered pairs of the form ((y,z),(z,y)).              *)
Definition Switch : Class := fun x =>
  exists y, exists z, x = :(:(y,z):,:(z,y):):.

Proposition SwitchCharac2 : forall (x x':U),
  Switch :(x,x'): <-> exists y, exists z, x = :(y,z): /\ x' = :(z,y):.
Proof.
  intros x x'. split; intros H1.
  - unfold Switch in H1. destruct H1 as [y [z H1]]. apply OrdPairEqual in H1.
    exists y. exists z. assumption.
  - destruct H1 as [y [z [H1 H2]]]. unfold Switch. exists y. exists z.
    rewrite H1, H2. reflexivity.
Qed.

Proposition SwitchIsFunctional : Functional Switch.
Proof.
  apply FunctionalCharac2. intros x x1 x2 H1 H2.
  apply SwitchCharac2 in H1. apply SwitchCharac2 in H2.
  destruct H1 as [y1 [z1 [H1 G1]]]. destruct H2 as [y2 [z2 [H2 G2]]].
  subst. apply OrdPairEqual in H2. destruct H2 as [H1 H2]. subst. reflexivity.
Qed.

(* The direct image of a class P by Switch is the converse of P.                *)
Proposition ImageBySwitch : forall (P:Class),
  Switch :[P]: :~: converse P.
Proof.
  intros P x. split; intros H1.
  - unfold image in H1. destruct H1 as [x' [H1 H2]]. apply SwitchCharac2 in H2.
    destruct H2 as [y [z [H2 H3]]]. apply ConverseCharac. exists y. exists z.
    subst. split.
    + reflexivity.
    + assumption.
  - apply ConverseCharac in H1. destruct H1 as [y [z [H1 H2]]]. subst.
    unfold image. exists :(y,z):. split.
    + assumption.
    + apply SwitchCharac2. exists y. exists z. split; reflexivity.
Qed.
