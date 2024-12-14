Require Import ZF.Binary.Converse.
Require Import ZF.Class.
Require Import ZF.Class.Binary.
Require Import ZF.Class.Include.
Require Import ZF.Class.Relation.
Require Import ZF.Core.Equiv.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* The converse of a class is the relation of the converse of its binary class. *)
Definition converse (P:Class) : Class := fromBinary (Converse.converse (toBinary P)).

(* Characterisation of the converse of a class.                                 *)
Proposition ConverseCharac : forall (P:Class) (x:U),
  converse P x <-> exists y, exists z, x = :(z,y): /\ P :(y,z):.
Proof.
  intros P x. split; intros H1.
  - unfold converse, Converse.converse, fromBinary, toBinary in H1.
    destruct H1 as [z [y H1]]. exists y. exists z. apply H1.
  - unfold converse, Converse.converse, fromBinary, toBinary.
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

(* The converse of a class is always a relation, even if the class is not.      *)
Proposition ConverseIsRelation : forall (P:Class), Relation (converse P).
Proof.
  intros P x H1. apply ConverseCharac in H1.
  destruct H1 as [y [z [H1 _]]]. exists z. exists y. apply H1.
Qed.

(* If the class P is a relation, then converse acting on P is idempotent.       *)
Proposition ConverseIdempotent : forall (P:Class),
  Relation P <-> converse (converse P) == P.
Proof.
  intros P. split; intros H1.
  - unfold converse.
    remember (Binary.Converse.converse (toBinary P)) as F eqn:Ef.
    apply EquivTran with (fromBinary (Binary.Converse.converse F)).
    + apply FromBinaryEquivCompat, ConverseEquivCompat, ToFromBinary.
    + rewrite Ef. clear Ef F. apply EquivTran with (fromBinary (toBinary P)).
      * apply FromBinaryEquivCompat. rewrite ConverseIdempotent.
        apply EquivRefl.
      * apply FromToBinary, H1.
  - intros x H2. apply H1 in H2. apply ConverseCharac in H2.
    destruct H2 as [y [z [H2 H3]]]. exists z. exists y. apply H2.
Qed.

(* The converse of the converse is a subclass of the original class.            *)
Proposition ConverseConverseIncl : forall (P:Class),
  converse (converse P) :<=: P.
Proof.
  intros P x H1. apply ConverseCharac in H1. destruct H1 as [y [z [H1 H2]]].
  apply ConverseCharac in H2. destruct H2 as [z' [y' [H2 H3]]].
  apply OrdPairEqual in H2. destruct H2 as [H2 H2']. subst. apply H3.
Qed.
