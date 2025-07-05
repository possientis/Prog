Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Relation.

Export ZF.Notation.Dot.

(* Composition of two sets.                                                     *)
Definition compose (g f:U) : U := fromClass (toClass g :.: toClass f)
  (Compose.IsSmall (toClass f) (toClass g) (SetIsSmall f) (SetIsSmall g)).

(* Notation "g :.: f" := (compose g f)                                          *)
Global Instance SetDot : Dot U := { dot := compose }.

(* The class of the composition is the composition of the classes.              *)
Proposition ToClass : forall (f g:U),
  toClass (g :.: f) :~: toClass g :.: toClass f.
Proof.
  intros f g. apply ToFromClass.
Qed.

Proposition Charac : forall (f g u:U),
  u :< g :.: f <-> exists x y z, u =:(x,z): /\ :(x,y): :< f /\ :(y,z): :< g.
Proof.
  intros f g u. split; intros H1.
  - apply FromClass.Charac in H1. destruct H1 as [x [y [z [H1 [H2 H3]]]]].
    exists x. exists y. exists z. split. 1: assumption. split; assumption.
  - destruct H1 as [x [y [z [H1 [H2 H3]]]]]. apply FromClass.Charac.
    exists x. exists y. exists z. split. 1: assumption. split; assumption.
Qed.

Proposition Charac2 : forall (f g x z:U),
  :(x,z): :< g :.: f <-> exists y, :(x,y): :< f /\ :(y, z): :< g.
Proof.
  intros f g x z. split; intros H1.
  - apply Charac in H1. destruct H1 as [x' [y [z' [H1 [H2 H3]]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H4]. subst.
    exists y. split; assumption.
  - destruct H1 as [y [H1 H2]]. apply Charac. exists x. exists y. exists z.
    split. 1: reflexivity. split; assumption.
Qed.

(* The composition of two sets is a relation.                                   *)
Proposition IsRelation : forall (f g:U), Relation (g :.: f).
Proof.
  intros f g u H1. apply Charac in H1. destruct H1 as [x [y [z [H1 _]]]].
  exists x. exists z. assumption.
Qed.

Proposition IsFunctional : forall (f g:U),
  Functional f -> Functional g -> Functional (g :.: f).
Proof.
  intros f g H1 H2 x z1 z2 H3 H4. apply Charac2 in H3. apply Charac2 in H4.
  destruct H3 as [y1 [H3 H5]]. destruct H4 as [y2 [H4 H6]].
  assert (y1 = y2) as H7. { apply H1 with x; assumption. }
  subst. apply H2 with y2; assumption.
Qed.

(* The converse of the composition is (almost) the composition of the converse. *)
Proposition Converse : forall (f g:U),
  (g :.: f)^:-1: = f^:-1: :.: g^:-1:.
Proof.
  intros f g. apply DoubleInclusion. split; intros u H1.
  - apply Converse.Charac in H1. destruct H1 as [x [z [H1 H2]]].
    apply Charac2 in H2. destruct H2 as [y [H2 H3]]. apply Charac.
    exists z. exists y. exists x. split. 1: assumption. split;
    apply Converse.Charac2Rev; assumption.
  - apply Charac in H1. destruct H1 as [z [y [x [H1 [H2 H3]]]]].
    apply Converse.Charac2 in H2. apply Converse.Charac2 in H3.
    apply Converse.Charac. exists x. exists z. split. 1: assumption.
    apply Charac2. exists y. split; assumption.
Qed.

(* The domain of the composition is a subset of the first domain.               *)
Proposition DomainIsSmaller : forall (f g:U),
  domain (g :.: f) :<=: domain f.
Proof.
  intros f g x H1.
Admitted.
