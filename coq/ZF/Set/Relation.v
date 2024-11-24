Require Import ZF.Axiom.Core.
Require Import ZF.Axiom.Replacement.
Require Import ZF.Class.Binary.
Require Import ZF.Set.OrdPair.

(* A relation is a set of ordered pairs.                                        *)
Definition Relation (a:U) : Prop :=
  forall x, x :< a -> exists y z, x = :(y,z):.

(* Functional set.                                                              *)
Definition Functional (a:U) : Prop :=
  forall x y z, :(x,y): :< a -> :(x,z): :< a -> y = z.

(* Binary class needed to define the converse of a set.                         *)
Definition Converse : Binary := fun x x' =>
  exists y z, x = :(y,z): /\ x' = :(z,y):.

(* This binary class is functional.                                             *)
Proposition ConverseFunctional : Binary.Functional Converse.
Proof.
  unfold Converse. intros x x1 x2 H1 H2.
  destruct H1 as [y [z [H1 H1']]]. destruct H2 as [y' [z' [H2 H2']]].
  rewrite H1 in H2. apply OrdPairEqual in H2. destruct H2 as [H2 H3].
  subst. reflexivity.
Qed.

(* The converse of a set converse a = { (z,y) | (y,z) :< a }                    *)
Definition converse (a:U) : U := replaceSet Converse a ConverseFunctional.

Proposition ConverseCharac : forall (a:U),
  forall x, x :< (converse a) <-> exists y z, x =:(y,z): /\ :(z,y): :< a.
Proof.
  intros a x. unfold converse. split; intros H1.
  - apply ReplaceCharac in H1. unfold Converse, image in H1.
    destruct H1 as [x' [H1 [y [z [H2 H3]]]]]. exists z. exists y. subst. split.
    + reflexivity.
    + apply H1.
  - destruct H1 as [y [z [H1 H2]]]. apply ReplaceCharac. unfold Converse, image.
    exists :(z,y):. split.
    + apply H2.
    + exists z. exists y. subst. split; reflexivity.
Qed.
