Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Image.

Proposition Charac : forall (f a x:U),
  x :< f^:-1: :[a]: <-> exists y, y :< a /\ :(x,y): :< f.
Proof.
  intros f a x. split; intros H1.
  - apply Image.Charac in H1. destruct H1 as [y [H1 H2]].
    apply Converse.Charac2 in H2. exists y. split; assumption.
  - destruct H1 as [y [H1 H2]]. apply Image.Charac. exists y.
    split. 1: assumption. apply Converse.Charac2Rev. assumption.
Admitted.
