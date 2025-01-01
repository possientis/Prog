Require Import ZF.Binary.
Require Import ZF.Class.
Require Import ZF.Class.Rel.
Require Import ZF.Core.Equiv.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* A binary class can be viewed as a class.                                     *)
Definition fromBinary (F:Binary) : Class := fun x =>
  exists y, exists z, x = :(y,z): /\ F y z.

(* The class associated with a binary class is indeed a relation class.         *)
Proposition FromBinaryIsRelation : forall (F:Binary), Rel (fromBinary F).
Proof.
  intros F x H1. unfold fromBinary in H1. destruct H1 as [y [z [H1 H2]]].
  exists y. exists z. apply H1.
Qed.

(* fromBinary is compatible with equivalences of classes and binary classes.    *)
Proposition FromBinaryEquivCompat : EquivCompat fromBinary.
Proof.
  intros F G H1 x. unfold fromBinary.
  split; intros H2;
  destruct H2 as [y [z [H2 H3]]]; exists y; exists z; split.
  - apply H2.
  - apply H1, H3.
  - apply H2.
  - apply H1, H3.
Qed.

(* A class can be viewed as a binary class.                                     *)
Definition toBinary (P:Class) : Binary := fun y z => P :(y,z):.

Proposition ToBinaryEquivCompat : EquivCompat toBinary.
Proof.
  intros P Q H1 x y. unfold toBinary. apply H1.
Qed.

(* The binary class of the class of a binary class F is F itself.               *)
Proposition ToFromBinary : forall (F:Binary), toBinary (fromBinary F) :~: F.
Proof.
  intros F. apply BinaryEquivCharac. intros y z.
  unfold toBinary, fromBinary. split; intros H1.
  - destruct H1 as [y' [z' [H1 H2]]]. apply OrdPairEqual in H1.
    destruct H1 as [H1 H1']. subst. apply H2.
  - exists y. exists z. split.
    + reflexivity.
    + apply H1.
Qed.

(* The relation class of the binary class of a relation class P is P itself.    *)
Proposition FromToBinary : forall (P:Class),
  Rel P -> fromBinary (toBinary P) :~: P.
Proof.
  intros P H1. apply ClassEquivCharac. intros x.
  unfold Rel in H1. unfold toBinary, fromBinary.
  split; intros H2.
  - destruct H2 as [y [z [H2 H3]]]. subst. apply H3.
  - destruct (H1 x H2) as [y [z H3]]. subst. exists y. exists z. split.
    + reflexivity.
    + apply H2.
Qed.

