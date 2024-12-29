Require Import ZF.Binary.
Require Import ZF.Binary.Converse.
Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.Functional.
Require Import ZF.Class.FromBinary.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Rel.
Require Import ZF.Class.Small.
Require Import ZF.Class.Switch.
Require Import ZF.Class.V.
Require Import ZF.Core.And.
Require Import ZF.Core.Dot.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Image.
Require Import ZF.Core.Leq.
Require Import ZF.Core.Prod.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* The converse of a class is the relation of the converse of its binary class. *)
Definition converse (P:Class) : Class
  := fromBinary (Binary.Converse.converse (toBinary P)).

(* Characterisation of the converse of a class.                                 *)
Proposition ConverseCharac : forall (P:Class) (x:U),
  converse P x <-> exists y, exists z, x = :(z,y): /\ P :(y,z):.
Proof.
  intros P x. split; intros H1.
  - unfold converse, Binary.Converse.converse, fromBinary, toBinary in H1.
    destruct H1 as [z [y H1]]. exists y. exists z. apply H1.
  - unfold converse, Binary.Converse.converse, fromBinary, toBinary.
    destruct H1 as [y [z H1]]. exists z. exists y. apply H1.
Qed.

(* A more useful characterisation when already dealing with an ordered pair.    *)
Proposition ConverseCharac2 : forall (P:Class) (y z:U),
  converse P :(y,z): <-> P :(z,y):.
Proof.
  intros P y z. split; intros H1.
  - apply ConverseCharac in H1.
    destruct H1 as [y' [z' [H1 H2]]]. apply OrdPairEqual in H1.
    destruct H1 as [H1 H1']. subst. apply H2.
  - apply ConverseCharac. exists z. exists y. split.
    + reflexivity.
    + apply H1.
Qed.

(* The direct image of a class P by Switch is the converse of P.                *)
Lemma ImageBySwitch : forall (P:Class),
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

Proposition ConverseIsSmall : forall (P:Class),
  Small P -> Small (converse P).
Proof.
  (* Let P be an arbitrary class. *)
  intros P.

  (* We assume that P is small. *)
  intros H1. assert (Small P) as A. { apply H1. } clear A.

  (* We need to show that converse(P) is small. *)
  assert (Small (converse P)) as A. 2: apply A.

  (* Using the equivalence Switch[P] ~ converse(P) ... *)
  apply SmallEquivCompat with Switch:[P]:. 1: apply ImageBySwitch.

  (* It is sufficient to show that Switch[P] is small. *)
  assert (Small (Switch:[P]:)) as A. 2: apply A.

  (* This follows from the fact that Switch is functional and P is small. *)
  apply ImageIsSmall.

  - apply SwitchIsFunctional.

  - apply H1.
Qed.

(* The converse of a class is always a relation, even if the class is not.      *)
Proposition ConverseIsRel : forall (P:Class), Rel (converse P).
Proof.
  intros P x H1. apply ConverseCharac in H1.
  destruct H1 as [y [z [H1 _]]]. exists z. exists y. apply H1.
Qed.

(* The converse of the converse is a subclass of the original class.            *)
Proposition ConverseConverseIncl : forall (P:Class),
  converse (converse P) :<=: P.
Proof.
  intros P x H1. apply ConverseCharac in H1. destruct H1 as [y [z [H1 H2]]].
  apply ConverseCharac in H2. destruct H2 as [z' [y' [H2 H3]]].
  apply OrdPairEqual in H2. destruct H2 as [H2 H2']. subst. apply H3.
Qed.

(* If the class P is a relation, then converse acting on P is idempotent.       *)
Proposition ConverseIsIdempotent : forall (P:Class),
  Rel P <-> converse (converse P) :~: P.
Proof.
  intros P. split; intros H1.
  - unfold converse.
    remember (Binary.Converse.converse (toBinary P)) as F eqn:Ef.
    apply ClassEquivTran with (fromBinary (Binary.Converse.converse F)).
    + apply FromBinaryEquivCompat, ConverseEquivCompat, ToFromBinary.
    + rewrite Ef. clear Ef F. apply ClassEquivTran with (fromBinary (toBinary P)).
      * apply FromBinaryEquivCompat. rewrite Binary.Converse.ConverseIdempotent.
        apply BinaryEquivRefl.
      * apply FromToBinary, H1.
  - intros x H2. apply H1 in H2. apply ConverseCharac in H2.
    destruct H2 as [y [z [H2 H3]]]. exists z. exists y. apply H2.
Qed.

Proposition ConverseOfCompose : forall (P Q:Class),
  converse (Q :.: P) :~: converse P :.: converse Q.
Proof.
  intros P Q u. split; intros H1.
  - apply ConverseCharac in H1. destruct H1 as [x [z [H1 H2]]].
    apply ComposeCharac2 in H2. destruct H2 as [y [H2 H3]].
    apply ComposeCharac. exists z. exists y. exists x. split.
    + assumption.
    + split; apply ConverseCharac2; assumption.
  - apply ComposeCharac in H1. destruct H1 as [z [y [x [H1 [H2 H3]]]]].
    apply (proj1 (ConverseCharac2 _ _ _)) in H2.
    apply (proj1 (ConverseCharac2 _ _ _)) in H3.
    apply ConverseCharac. exists x. exists z. split.
    + assumption.
    + apply ComposeCharac2. exists y. split; assumption.
Qed.

(* Only keep ordered pairs of a class: you get the same converse.               *)
Proposition ConverseKeepOrderedPairs : forall (P:Class),
  converse P :~: converse (P :/\: V:x:V).
Proof.
  intros P x. split; intros H1.
  - apply ConverseCharac in H1. destruct H1 as [y [z [H1 H2]]].
    apply ConverseCharac. exists y. exists z. split.
    + assumption.
    + split.
      * assumption.
      * apply ProdCharac2. split; apply I.
  - apply ConverseCharac in H1. destruct H1 as [y [z [H1 [H2 _]]]].
    apply ConverseCharac. exists y. exists z. split; assumption.
Qed.
