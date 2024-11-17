Require Import ZF.Axiom.Core.
Require Import ZF.Class.Binary.
Require Import ZF.Class.Class.
Require Import ZF.Core.Equiv.
Require Import ZF.Set.OrdPair.

(* Predicate on classes, expressing the fact that a class is a 'relation class' *)
(* i.e. a class whose 'elements' are ordered pairs.                             *)
Definition Relation (P:Class) : Prop :=
    forall x, P x -> exists y, exists z, x = :(y,z):.

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
Definition toBinary (P:Class) : Binary := fun y z => P :(y,z):.

(* The binary class of the relation class of a binary class F is F itself.      *)
Proposition ToFromBinary : forall (F:Binary), toBinary (fromBinary F) == F.
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
  Relation P -> fromBinary (toBinary P) == P.
Proof.
  intros P H1. apply ClassEquivCharac. intros x.
  unfold Relation in H1. unfold toBinary, fromBinary.
  split; intros H2.
  - destruct H2 as [y [z [H2 H3]]]. subst. apply H3.
  - destruct (H1 x H2) as [y [z H3]]. subst. exists y. exists z. split.
    + reflexivity.
    + apply H2.
Qed.

(* A class is said to be functional if its associated binary class is           *)
Definition Functional (P:Class) : Prop := Binary.Functional (toBinary P).

(* Characterisation of a functional class.                                      *)
Proposition FunctionalCharac : forall (P:Class), Functional P <->
  forall x, forall y, forall z, P :(x,y): -> P :(x,z): -> y = z.
Proof.
  intros P. unfold Functional, Binary. split; intros H1.
  - unfold Functional, Binary.Functional, toBinary in H1. apply H1.
  - unfold Functional, Binary.Functional, toBinary. apply H1.
Qed.

(* The converse of a class is the relation of the converse of its binary class. *)
Definition converse (P:Class) : Class := fromBinary (Binary.converse (toBinary P)).

(* Characterisation of the converse of a class.                                 *)
Proposition ConverseCharac : forall (P:Class) (x:U),
  converse P x <-> exists y, exists z, x = :(y,z): /\ P :(z,y):.
Proof.
  intros P x. unfold converse, Binary.converse, fromBinary, toBinary.
  split; intros H1; apply H1.
Qed.

(* A more useful characterisation when already dealing with an ordered pair.    *)
Proposition ConverseCharac2 : forall (P:Class) (y z:U),
  converse P :(y,z): <-> P :(z,y):.
Proof.
  intros P y z. split; intros H1.
    (* Not clear why 'proj1' was needed here *)
  - apply (proj1 (ConverseCharac P :(y,z):)) in H1.
    destruct H1 as [y' [z' [H1 H2]]]. apply OrdPairEqual in H1.
    destruct H1 as [H1 H1']. subst. apply H2.
  - apply ConverseCharac. exists y. exists z. split.
    + reflexivity.
    + apply H1.
Qed.

(*
(* If the class P is relation, then converse acting on P is idempotent.         *)
Proposition ConverseIdempotent : forall (P:Class) (x:U),
  Relation P -> converse (converse P) x <-> P x.
Proof.
  intros P x H1. unfold converse.
  remember (Binary.converse (toBinary P)) as F eqn:EF.
  remember (toBinary (fromBinary F)) as G eqn:EG.
  remember (fromBinary (Binary.converse G)) as Q eqn:HQ.
  (* Not clear why 'proj1' was needed here *)
  apply (proj1 (ClassEquivCharac Q P)).
Show.
*)
