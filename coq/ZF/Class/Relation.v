Require Import ZF.Axiom.Core.
Require Import ZF.Class.Binary.
Require Import ZF.Class.Class.
Require Import ZF.Set.OrdPair.

(* Predicate on classes, expressing the fact that a class is a 'relation class' *)
(* i.e. a class whose 'elements' are ordered pairs.                             *)
Definition Relation (R:Class) : Prop :=
    forall x, R x -> exists y, exists z, x = :(y,z):.

(* A binary class can be viewed as a relation class.                            *)
Definition fromBinary (F:Binary) : Class := fun x =>
  exists y, exists z, x = :(y,z): /\ F y z.

(* The class associated with a binary class is indeed a class relation.         *)
Proposition FromBinaryIsRelation : forall (F:Binary),
  Relation (fromBinary F).
Proof.
  intros F x H1. unfold fromBinary in H1. destruct H1 as [y [z [H1 H2]]].
  exists y. exists z. apply H1.
Qed.

(* A class can be viewed as a binary class.                                     *)
Definition toBinary (R:Class) : Binary := fun y z => R :(y,z):.

(* The binary class of the relation class of a binary class F is F itself.      *)
Proposition ToFromBinary : forall (F:Binary), forall (y z:U),
  toBinary (fromBinary F) y z <-> F y z.
Proof.
  intros F y z. unfold toBinary, fromBinary. split; intros H1.
  - destruct H1 as [y' [z' [H1 H2]]]. apply OrdPairEqual in H1.
    destruct H1 as [H1 H1']. subst. apply H2.
  - exists y. exists z. split.
    + reflexivity.
    + apply H1.
Qed.

(* The relation class of the binary class of a relation class R is R itself.    *)
Proposition FromToBinary : forall (R:Class), forall (x:U),
  Relation R -> fromBinary (toBinary R) x <-> R x.
Proof.
  intros R x H1. unfold Relation in H1. unfold toBinary, fromBinary.
  split; intros H2.
  - destruct H2 as [y [z [H2 H3]]]. subst. apply H3.
  - destruct (H1 x H2) as [y [z H3]]. subst. exists y. exists z. split.
    + reflexivity.
    + apply H2.
Qed.
