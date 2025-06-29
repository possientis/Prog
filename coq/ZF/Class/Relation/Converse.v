Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Relation.Switch.
Require Import ZF.Class.Small.
Require Import ZF.Class.V.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

Require Import ZF.Notation.Inverse.
Export ZF.Notation.Inverse.

(* The converse of a class is the relation of the converse of its binary class. *)
Definition converse (F:Class) : Class := fun x =>
  exists y z, x = :(z,y): /\ F :(y,z):.

(* Notation "F ^:-1:" := (converse F)                                           *)
Global Instance ClassInverse : Inverse Class := { inverse := converse }.

Proposition Charac2 : forall (F:Class) (y z:U),
  F^:-1: :(y,z): -> F :(z,y):.
Proof.
  intros F y z [y' [z' [H1 H2]]]. apply OrdPair.WhenEqual in H1.
  destruct H1 as [H1 H1']. subst. assumption.
Qed.

Proposition Charac2Rev : forall (F:Class) (y z:U),
  F :(z,y): -> F^:-1: :(y,z):.
Proof.
  intros F y z H1. exists z. exists y. split. 1: reflexivity. assumption.
Qed.

Proposition EquivCompat : forall (F G:Class),
  F :~: G -> F^:-1: :~: G^:-1:.
Proof.
  intros F G H1 x. split; intros H2; destruct H2 as [y [z [H2 H3]]];
  exists y; exists z; split; try assumption; apply H1; assumption.
Qed.

Proposition InclCompat : forall (F G:Class),
  F :<=: G -> F^:-1: :<=: G^:-1:.
Proof.
  intros F G H1 x H2. destruct H2 as [y [z [H2 H3]]]. subst.
  exists y. exists z. split. 1: reflexivity. apply H1. assumption.
Qed.

(* The converse is the direct image by Switch.                                  *)
Lemma IsImageBySwitch : forall (F:Class),
 F^:-1: :~: Switch :[F]:.
Proof.
  intros F x. split; intros H1.
  - destruct H1 as [y [z [H1 H2]]]. subst. exists :(y,z):. split.
    + assumption.
    + apply Switch.Charac2. exists y. exists z. split; reflexivity.
  - destruct H1 as [x' [H1 H2]]. apply Switch.Charac2 in H2.
    destruct H2 as [y [z [H2 H3]]]. exists y. exists z. subst. split.
    + reflexivity.
    + assumption.
Qed.

Proposition IsSmall : forall (F:Class),
  Small F -> Small F^:-1:.
Proof.
  (* Let F be an arbitrary class. *)
  intros F.

  (* We assume that F is small. *)
  intros H1. assert (Small F) as A. { apply H1. } clear A.

  (* We need to show that converse(F) is small. *)
  assert (Small F^:-1:) as A. 2: apply A.

  (* Using the equivalence converse(F) ~ Switch[F] ... *)
  apply Small.EquivCompat with Switch:[F]:.
    1: { apply EquivSym, IsImageBySwitch. }

  (* It is sufficient to show that Switch[F] is small. *)
  assert (Small (Switch:[F]:)) as A. 2: apply A.

  (* This follows from the fact that Switch is functional and F is small. *)
  apply Image.IsSmall.

  - apply Switch.IsFunctional.

  - apply H1.
Qed.

(* The converse of a class is always a relation, even if the class is not.      *)
Proposition IsRelation : forall (F:Class), Relation F^:-1:.
Proof.
  intros F x H1.
  destruct H1 as [y [z [H1 _]]]. exists z. exists y. apply H1.
Qed.

(* The converse of the converse is a subclass of the original class.            *)
Proposition IsIncl : forall (F:Class),
  (F^:-1:)^:-1: :<=: F.
Proof.
  intros F x H1. destruct H1 as [y [z [H1 H2]]].
  apply Charac2 in H2. subst. assumption.
Qed.

(* A class is a relation iff the converse acting on it is idempotent.           *)
Proposition IsIdempotent : forall (F:Class),
  Relation F <-> (F^:-1:)^:-1: :~: F.
Proof.
  intros F. split; intros H1.
  - intros x. split; intros H2.
    + specialize (H1 x). destruct H2 as [y [z [H2 H3]]]. subst.
      apply Charac2 in H3. assumption.
    + specialize (H1 x H2). destruct H1 as [y [z H1]]. subst.
      apply Charac2Rev, Charac2Rev. assumption.
  - apply Relation.EquivCompat with (F^:-1:)^:-1:. 1: assumption.
    apply IsRelation.
Qed.

(* The converse is the converse of the subclass of ordered pairs.               *)
Proposition IsConverseOfOrderedPairs : forall (F:Class),
  F^:-1: :~: (F :/\: V:x:V)^:-1:.
Proof.
  intros F x. split; intros H1.
  - destruct H1 as [y [z [H1 H2]]]. exists y. exists z. split.
    + assumption.
    + split.
      * assumption.
      * apply Prod.Charac2. split; apply I.
  - destruct H1 as [y [z [H1 [H2 _]]]]. exists y. exists z. split; assumption.
Qed.

(* The domain of the converse is the range.                                     *)
Proposition Domain : forall (F:Class),
  domain F^:-1: :~: range F.
Proof.
  intros F y. split; intros H1.
  - destruct H1 as [x H1]. apply Charac2 in H1.
    exists x. assumption.
  - destruct H1 as [x H1]. exists x. apply Charac2Rev. assumption.
Qed.

(* The range of the converse is the domain.                                     *)
Proposition Range : forall (F:Class),
  range F^:-1: :~: domain F.
Proof.
  intros F x. split; intros H1.
  - destruct H1 as [y H1]. apply Charac2 in H1.
    exists y. assumption.
  - destruct H1 as [y H1]. exists y. apply Charac2Rev. assumption.
Qed.

Proposition WhenFunctional : forall (F:Class) (x y z:U),
  Functional F^:-1: -> F :(x,z): -> F :(y,z): -> x = y.
Proof.
  intros F x y z H1 H2 H3. apply H1 with z; apply Charac2Rev; assumption.
Qed.

Proposition Inter2Image : forall (F A B:Class), Functional F^:-1: ->
  F:[A :/\: B]: :~: F:[A]: :/\: F:[B]:.
Proof.
  intros F A B H1. apply DoubleInclusion. split.
  - apply Inter2.Image.
  - intros y [[a [H2 H3]] [b [H4 H5]]].
    assert (a = b) as H6. { apply WhenFunctional with F y; assumption. }
    subst. exists b. split. 2: assumption. split; assumption.
Qed.
