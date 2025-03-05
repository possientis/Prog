Require Import ZF.Class.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Range.
Require Import ZF.Class.Relation.
Require Import ZF.Class.Small.
Require Import ZF.Class.Switch.
Require Import ZF.Class.V.
Require Import ZF.Core.Inverse.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.
Export ZF.Core.Inverse.

(* The converse of a class is the relation of the converse of its binary class. *)
Definition converse (F:Class) : Class := fun x =>
  exists y z, x = :(z,y): /\ F :(y,z):.

(* Notation "F ^:-1:" := (converse F)                                           *)
Global Instance ClassInverse : Inverse Class := { inverse := converse }.

Proposition ConverseCharac2 : forall (F:Class) (y z:U),
  F^:-1: :(y,z): <-> F :(z,y):.
Proof.
  intros F y z. split; intros H1.
  - destruct H1 as [y' [z' [H1 H2]]]. apply OrdPairEqual in H1.
    destruct H1 as [H1 H1']. subst. apply H2.
  - exists z. exists y. split. 1: reflexivity. apply H1.
Qed.


Proposition ConverseEquivCompat : forall (F G:Class),
  F :~: G -> F^:-1: :~: G^:-1:.
Proof.
  intros F G H1 x. split; intros H2; destruct H2 as [y [z [H2 H3]]];
  exists y; exists z; split; try assumption; apply H1; assumption.
Qed.

Proposition ConverseInclCompat : forall (F G:Class),
  F :<=: G -> F^:-1: :<=: G^:-1:.
Proof.
  intros F G H1 x H2. destruct H2 as [y [z [H2 H3]]]. subst.
  exists y. exists z. split. 1: reflexivity. apply H1. assumption.
Qed.

(* The converse is the direct image by Switch.                                  *)
Lemma ConverseIsImageBySwitch : forall (F:Class),
 F^:-1: :~: Switch :[F]:.
Proof.
  intros F x. split; intros H1.
  - destruct H1 as [y [z [H1 H2]]]. subst. exists :(y,z):. split.
    + assumption.
    + apply SwitchCharac2. exists y. exists z. split; reflexivity.
  - destruct H1 as [x' [H1 H2]]. apply SwitchCharac2 in H2.
    destruct H2 as [y [z [H2 H3]]]. exists y. exists z. subst. split.
    + reflexivity.
    + assumption.
Qed.

Proposition ConverseIsSmall : forall (F:Class),
  Small F -> Small F^:-1:.
Proof.
  (* Let F be an arbitrary class. *)
  intros F.

  (* We assume that F is small. *)
  intros H1. assert (Small F) as A. { apply H1. } clear A.

  (* We need to show that converse(F) is small. *)
  assert (Small F^:-1:) as A. 2: apply A.

  (* Using the equivalence converse(F) ~ Switch[F] ... *)
  apply SmallEquivCompat with Switch:[F]:.
    1: { apply ClassEquivSym, ConverseIsImageBySwitch. }

  (* It is sufficient to show that Switch[F] is small. *)
  assert (Small (Switch:[F]:)) as A. 2: apply A.

  (* This follows from the fact that Switch is functional and F is small. *)
  apply ImageIsSmall.

  - apply SwitchIsFunctional.

  - apply H1.
Qed.

(* The converse of a class is always a relation, even if the class is not.      *)
Proposition ConverseIsRelation : forall (F:Class), Relation F^:-1:.
Proof.
  intros F x H1.
  destruct H1 as [y [z [H1 _]]]. exists z. exists y. apply H1.
Qed.

(* The converse of the converse is a subclass of the original class.            *)
Proposition ConverseOfConverseIncl : forall (F:Class),
  (F^:-1:)^:-1: :<=: F.
Proof.
  intros F x H1.
  destruct H1 as [y [z [H1 H2]]]. destruct H2 as [z' [y' [H2 H3]]].
  apply OrdPairEqual in H2. destruct H2 as [H2 H2']. subst. apply H3.
Qed.


(* A class is a relation iff the converse acting on it is idempotent.           *)
Proposition ConverseIsIdempotent : forall (F:Class),
  Relation F <-> (F^:-1:)^:-1: :~: F.
Proof.
  intros F. split; intros H1.
  - intros x. split; intros H2.
    + specialize (H1 x). destruct H2 as [z [y [H2 H3]]]. subst.
      destruct H3 as [y' [z' [H3 H4]]]. apply OrdPairEqual in H3.
      destruct H3 as [H3 H5]. subst. assumption.
    + specialize (H1 x H2). destruct H1 as [y [z H1]].
      exists z. exists y. split. 1: assumption. exists y. exists z.
      split. 1: reflexivity. subst. assumption.
  - intros x H2. apply H1 in H2. destruct H2 as [z [y [H2 H3]]].
    exists y. exists z. assumption.
Qed.

(* The converse is the converse of the subclass of ordered pairs.               *)
Proposition ConverseIsConverseOfOrderedPairs : forall (F:Class),
  F^:-1: :~: (F :/\: V:x:V)^:-1:.
Proof.
  intros F x. split; intros H1.
  - destruct H1 as [y [z [H1 H2]]]. exists y. exists z. split.
    + assumption.
    + split.
      * assumption.
      * apply ProdCharac2. split; apply I.
  - destruct H1 as [y [z [H1 [H2 _]]]]. exists y. exists z. split; assumption.
Qed.

Proposition ConverseDomain : forall (F:Class),
  domain F^:-1: :~: range F.
Proof.
  intros F y. split; intros H1.
  - destruct H1 as [x H1]. apply (proj1 (ConverseCharac2 _ _ _)) in H1.
    exists x. assumption.
  - destruct H1 as [x H1]. exists x. apply ConverseCharac2. assumption.
Qed.

Proposition ConverseRange : forall (F:Class),
  range F^:-1: :~: domain F.
Proof.
  intros F x. split; intros H1.
  - destruct H1 as [y H1]. apply (proj1 (ConverseCharac2 _ _ _)) in H1.
    exists y. assumption.
  - destruct H1 as [y H1]. exists y. apply ConverseCharac2. assumption.
Qed.
