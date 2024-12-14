Declare Scope ZF_Class_Relation_scope.

Require Import ZF.Set.
Require Import ZF.Class.
Require Import ZF.Binary.
Require Import ZF.Binary.Converse.
Require Import ZF.Binary.Domain.
Require Import ZF.Binary.Range.
Require Import ZF.Binary.Restrict.
Require Import ZF.Class.Intersect.
Require Import ZF.Core.Equiv.
Require Import ZF.Set.OrdPair.

Open Scope ZF_Class_Relation_scope.

(* Predicate on classes, expressing the fact that a class is a 'relation class' *)
(* i.e. a class whose 'elements' are ordered pairs.                             *)
Definition Relation (P:Class) : Prop :=
    forall x, P x -> exists y, exists z, x = :(y,z):.

(* A binary class can be viewed as a relation class.                            *)
Definition fromBinary (F:Binary) : Class := fun x =>
  exists y, exists z, x = :(y,z): /\ F y z.

(* fromBinary is compatible with equivalences of classes and binary classes.    *)
Proposition FromBinaryEquivCompat : EquivCompat fromBinary.
Proof.
  intros F G H1 x. unfold fromBinary. split; intros H2;
  destruct H2 as [y [z [H2 H3]]]; exists y; exists z; split.
  - apply H2.
  - apply H1, H3.
  - apply H2.
  - apply H1, H3.
Qed.

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
Definition Functional (P:Class) : Prop := Functional.Functional (toBinary P).

(* Characterisation of a functional class (only one side for quick unfolding).  *)
Proposition FunctionalCharac : forall (P:Class), Functional P ->
  forall x y z, P :(x,y): -> P :(x,z): -> y = z.
Proof.
  intros P H1. apply H1.
Qed.

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

(* If the class P is relation, then converse acting on P is idempotent.         *)
Proposition ConverseIdempotent : forall (P:Class),
  Relation P <-> converse (converse P) == P.
Proof.
  intros P. split; intros H1.
  - unfold converse.
    remember (Converse.converse (toBinary P)) as F eqn:Ef.
    apply EquivTran with (fromBinary (Converse.converse F)).
    + apply FromBinaryEquivCompat, ConverseEquivCompat, ToFromBinary.
    + rewrite Ef. clear Ef F. apply EquivTran with (fromBinary (toBinary P)).
      * apply FromBinaryEquivCompat. rewrite ConverseIdempotent.
        apply EquivRefl.
      * apply FromToBinary, H1.
  - intros x H2. apply H1 in H2. apply ConverseCharac in H2.
    destruct H2 as [y [z [H2 H3]]]. exists z. exists y. apply H2.
Qed.

(* A class is 'one-to-one' if both itself and its converse are functional.      *)
Definition OneToOne (P:Class) : Prop := Functional P /\ Functional (converse P).

Proposition OneToOneCharac1 : forall (P:Class), OneToOne P ->
  forall x, forall y, forall z, P :(x,y): -> P :(x,z): -> y = z.
Proof.
  intros P H1. apply FunctionalCharac, H1.
Qed.

Proposition OneToOneCharac2 : forall (P:Class), OneToOne P ->
  forall x, forall y, forall z, P :(y,x): -> P :(z,x): -> y = z.
Proof.
  intros P H1 x y z H3 H4. destruct H1 as [H1 H2].
  apply FunctionalCharac with (converse P) x.
  - apply H2.
  - apply ConverseCharac2, H3.
  - apply ConverseCharac2, H4.
Qed.

(* A class is a function if it is a relation and it is functional.              *)
Definition Function (P:Class) : Prop := Relation P /\ Functional P.

(* A class is a bijection if it is a relation and it is one-to-one.             *)
Definition Bijection (P:Class) : Prop := Relation P /\ OneToOne P.

Proposition BijectionIsFunction : forall (P:Class),
  Bijection P -> Function P.
Proof.
  intros P [H1 [H2 H3]]. split; assumption.
Qed.

Proposition BijectionConverseIsFunction : forall (P:Class),
  Bijection P -> Function (converse P).
Proof.
  intros P [H1 [H2 H3]]. split.
  - apply ConverseIsRelation.
  - apply H3.
Qed.

(* The domain of a class is the domain of its binary class.                     *)
Definition domain (P:Class) : Class := Domain.domain (toBinary P).

(* The range of a class is the range of its binary class.                       *)
Definition range (P:Class) : Class := Range.range (toBinary P).

(* Quick unfolding.                                                             *)
Proposition DomainCharac : forall (P:Class) (x:U),
  domain P x <-> exists y, P :(x,y):.
Proof.
  intros P x. split; intros H1.
  - apply H1.
  - apply H1.
Qed.

(* Quick unfolding.                                                             *)
Proposition RangeCharac : forall (P:Class) (y:U),
  range P y <-> exists x, P :(x,y):.
Proof.
  intros P y. split; intros H1.
  - apply H1.
  - apply H1.
Qed.

(* Restricting a class P to a class Q.                                          *)
Definition restrict (P Q:Class) : Class
  := fromBinary (Restrict.restrict (toBinary P) Q).

Notation "P :|: Q" := (restrict P Q)
  (at level 13, left associativity) : ZF_Class_Relation_scope.

Proposition RestrictCharac : forall (P Q:Class) (x:U),
  (P:|:Q) x -> exists y, exists z, x = :(y,z): /\ Q y /\ P :(y,z):.
Proof.
  intros P Q x H1. apply H1.
Qed.

Proposition RestrictCharac2 : forall (P Q:Class) (y z:U),
  (P:|:Q) :(y,z): <-> Q y /\ P :(y,z):.
Proof.
  intros P Q y z. split; intros H1.
  - apply RestrictCharac in H1.
    destruct H1 as [y' [z' [H1 H2]]]. apply OrdPairEqual in H1.
    destruct H1 as [H1 H1']. subst. apply H2.
  - exists y. exists z. split.
    + reflexivity.
    + apply H1.
Qed.

Proposition RestrictIsRelation : forall (P Q:Class),
  Relation (P:|:Q).
Proof.
  intros P Q. apply FromBinaryIsRelation.
Qed.

Proposition DomainOfRestrict : forall (P Q:Class),
  domain (P:|:Q) == Q :/\: domain P.
Proof.
  intros P Q x. split; intros H1.
  - apply (proj1 (DomainCharac (P:|:Q) x)) in H1. destruct H1 as [y H1].
    apply RestrictCharac2 in H1. destruct H1 as [H1 H2]. split.
    + apply H1.
    + apply DomainCharac. exists y. apply H2.
  - destruct H1 as [H1 H2]. apply (proj1 (DomainCharac P x)) in H2.
    destruct H2 as [y H2]. apply DomainCharac. exists y. apply RestrictCharac2.
    split; assumption.
Qed.

(* Direct image of a set by a class P.                                          *)
Definition image (P:Class) (a:U) : Class := Image.image (toBinary P) a.

Notation "P :[ a ]:" := (image P a)
  (at level 0, no associativity) : ZF_Class_Relation_scope.

Proposition ImageCharac : forall (P:Class) (a y:U),
  P:[a]: y -> exists x, x :< a /\ P :(x,y):.
Proof.
  intros P a y H1. apply H1.
Qed.

Proposition ImageIsRestriction : forall (P:Class) (a:U),
  P:[a]: == range (P:|:(toClass a)).
Proof.
  intros P a y. split; intros H1.
  - apply ImageCharac in H1. destruct H1 as [x [H1 H2]].
    exists x. unfold toBinary. apply RestrictCharac2. split; assumption.
  - apply RangeCharac in H1. destruct H1 as [x H1]. apply RestrictCharac2 in H1.
    destruct H1 as [H1 H2]. exists x. unfold toBinary. split; assumption.
Qed.

