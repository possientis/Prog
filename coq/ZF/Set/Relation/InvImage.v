Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Image.

Export ZF.Notation.Image.
Export ZF.Notation.Inverse.

Proposition Charac : forall (f a x:U),
  x :< f^:-1: :[a]: <-> exists y, y :< a /\ :(x,y): :< f.
Proof.
  intros f a x. split; intros H1.
  - apply Image.Charac in H1. destruct H1 as [y [H1 H2]].
    apply Converse.Charac2 in H2. exists y. split; assumption.
  - destruct H1 as [y [H1 H2]]. apply Image.Charac. exists y.
    split. 1: assumption. apply Converse.Charac2Rev. assumption.
Qed.

(* The inverse image is compatible with set inclusion.                          *)
Proposition InclCompat : forall (f g a b:U),
  f :<=: g -> a :<=: b -> f^:-1: :[a]: :<=: g^:-1: :[b]:.
Proof.
  intros f g a b H1 H2. apply Image.InclCompat. 2: assumption.
  apply Converse.InclCompat. assumption.
Qed.

(* The inverse image is left-compatible with set inclusion.                     *)
Proposition InclCompatL : forall (f g a:U),
  f :<=: g -> f^:-1: :[a]: :<=: g^:-1: :[a]:.
Proof.
  intros f g a H1. apply InclCompat.
  - assumption.
  - apply Incl.Refl.
Qed.

(* The inverse image is right-compatible with set inclusion.                    *)
Proposition InclCompatR : forall (f a b:U),
  a :<=: b -> f^:-1: :[a]: :<=: f^:-1: :[b]:.
Proof.
  intros f a b H1. apply InclCompat.
  - apply Incl.Refl.
  - assumption.
Qed.

