Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Specify.

Export ZF.Notation.Pipe.

Definition restrict (f:U) (A:Class) : U := fromClass (toClass f :|: A)
  (Restrict.IsSmall' (toClass f) A (SetIsSmall f)).

(* Notation "f :|: A" := (restrict f A)                                         *)
Global Instance SetByClassPipe : Pipe U Class U := { pipe := restrict }.

Proposition ToClass : forall (A:Class) (f:U), 
  toClass (f :|: A) :~: toClass f :|: A.
Proof.
  intros A f. apply FromClass.ToFromClass.
Qed.

Proposition EquivCompat : forall (A B:Class) (f:U),
  A :~: B -> f:|:A = f:|:B.
Proof.
  intros A B f H1. 
  apply FromClass.EquivCompat, Restrict.EquivCompatR. assumption.
Qed.

Proposition Charac : forall (A:Class) (f x:U),
  x :< f:|:A <-> exists y z, x = :(y,z): /\ A y /\ :(y, z): :< f.
Proof.
  intros A f x. split; intros H1.
  - apply FromClass.Charac in H1. destruct H1 as [y [z [H1 [H2 H3]]]].
    exists y. exists z. split. 1: assumption. split; assumption.
  - destruct H1 as [y [z [H1 [H2 H3]]]]. apply FromClass.Charac.
    exists y. exists z. split. 1: assumption. split; assumption.
Qed.

Proposition Charac2 : forall (A:Class) (f y z:U), 
  :(y,z): :< f:|:A <-> A y /\ :(y,z): :< f.
Proof.
  intros A f y z. split; intros H1.
  - apply Charac in H1. destruct H1 as [y' [z' [H1 [H2 H3]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H4]. subst.
    split; assumption.
  - apply Charac. exists y. exists z. split. 2: assumption. reflexivity. 
Qed.

(* The restriction of a set by a class is always a relation.                    *)
Proposition IsRelation : forall (A:Class) (f:U),
  Relation (f:|:A).
Proof.
  intros A f x H1. apply Charac in H1. destruct H1 as [y [z [H1 _]]].
  exists y. exists z. assumption.
Qed.

(* The restriction of a functional set is a functional set.                     *)
Proposition IsFunctional : forall (A:Class) (f:U),
  Functional f -> Functional (f:|:A).
Proof.
  intros A f H1 x y z H2 H3.
  apply Charac2 in H2. destruct H2 as [_ H2].
  apply Charac2 in H3. destruct H3 as [_ H3].
  apply H1 with x; assumption.
Qed.

Proposition IsFunction : forall (A:Class) (f:U),
  Functional f -> Function (f:|:A).
Proof.
  intros A f H1. split.
  - apply IsRelation.
  - apply IsFunctional. assumption.
Qed.

Proposition DomainOf : forall (A:Class) (f:U),
  domain (f:|:A) = :{ domain f | A }:.
Proof.
  intros A f. apply DoubleInclusion. split; intros x H1.
  - apply Domain.Charac in H1. destruct H1 as [y H1]. 
    apply Charac2 in H1. destruct H1 as [H1 H2].
    apply Specify.Charac. split. 2: assumption.
    apply Domain.Charac. exists y. assumption.
  - apply Specify.Charac in H1. destruct H1 as [H1 H2].
    apply Domain.Charac in H1. destruct H1 as [y H1]. 
    apply Domain.Charac. exists y. 
    apply Charac2. split; assumption.
Qed.
