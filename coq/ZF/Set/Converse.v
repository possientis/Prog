Require Import ZF.Binary.
Require Import ZF.Binary.Functional.
Require Import ZF.Binary.Image.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Replace.


(* Binary class needed to define the converse of a set.                         *)
Definition Converse : Binary := fun x x' =>
  exists y z, x = :(y,z): /\ x' = :(z,y):.

(* This binary class is functional.                                             *)
Proposition ConverseFunctional : Functional Converse.
Proof.
  unfold Converse. intros x x1 x2 H1 H2.
  destruct H1 as [y [z [H1 H1']]]. destruct H2 as [y' [z' [H2 H2']]].
  rewrite H1 in H2. apply OrdPairEqual in H2. destruct H2 as [H2 H3].
  subst. reflexivity.
Qed.

(* The converse of a set converse a = { (z,y) | (y,z) :< a }                    *)
Definition converse (a:U) : U := replaceSet Converse a ConverseFunctional.

Proposition ConverseCharac : forall (a:U),
  forall x, x :< (converse a) <-> exists y z, x =:(z,y): /\ :(y,z): :< a.
Proof.
  intros a x. unfold converse. split; intros H1.
  - apply ReplaceCharac in H1. unfold Converse, image in H1.
    destruct H1 as [x' [H1 [y [z [H2 H3]]]]]. exists y. exists z. subst. split.
    + reflexivity.
    + apply H1.
  - destruct H1 as [y [z [H1 H2]]]. apply ReplaceCharac. unfold Converse, image.
    exists :(y,z):. split.
    + apply H2.
    + exists y. exists z. subst. split; reflexivity.
Qed.
