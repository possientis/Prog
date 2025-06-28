Require Import ZF.Class.Core.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Relation.

Export ZF.Notation.Inverse.

(* The converse of a set.                                                       *)
Definition converse (f:U) : U := fromClass (toClass f)^:-1:
  (Converse.IsSmall (toClass f) (SetIsSmall f)).

(* Notation "f ^:-1:" := (converse f)                                           *)
Global Instance SetInverse : Inverse U := { inverse := converse }.

(* The class of the converse is the converse of the class.                      *)
Proposition ToClass : forall (f:U),
  toClass f^:-1: :~: (toClass f)^:-1:.
Proof.
  intros f. apply ToFromClass.
Qed.

Proposition Charac : forall (f x:U),
  x :< f^:-1: <-> exists y z, x = :(z,y): /\ :(y,z): :< f.
Proof.
  intros f x. split; intros H1.
  - apply FromClass.Charac in H1. destruct H1 as [y [z [H1 H2]]].
    exists y. exists z. split; assumption.
  - destruct H1 as [y [z [H1 H2]]]. apply FromClass.Charac.
    exists y. exists z. split; assumption.
Qed.

Proposition Charac2 : forall (f y z:U),
  :(y,z): :< f^:-1: -> :(z,y): :< f.
Proof.
  intros f y z H1. apply Charac in H1. destruct H1 as [z' [y' [H1 H2]]].
  apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3]. subst. assumption.
Qed.

Proposition CharacRev : forall (f y z:U),
  :(z,y): :< f -> :(y,z): :< f^:-1:.
Proof.
  intros f y z H1. apply Charac. exists z. exists y. split.
  1: reflexivity. assumption.
Qed.

(* The converse operation is compatible with set inclusion.                     *)
Proposition InclCompat : forall (f g:U),
  f :<=: g -> f^:-1: :<=: g^:-1:.
Proof.
  intros  f g H1 x H2.
  apply Charac in H2. destruct H2 as [y [z [H2 H3]]]. subst. apply Charac.
  exists y. exists z. split. 1: reflexivity. apply H1. assumption.
Qed.

(* The converse of a set if a relation.                                         *)
Proposition IsRelation : forall (f:U), Relation f^:-1:.
Proof.
  intros f x H1. apply Charac in H1. destruct H1 as [y [z [H1 H2]]].
  exists z. exists y. assumption.
Qed.

(* The converse of the converse is a subset of the original set.                *)
Proposition IsIncl : forall (f:U),
  (f^:-1:)^:-1: :<=: f.
Proof.
Admitted.

