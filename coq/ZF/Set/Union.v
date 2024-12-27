Require Import ZF.Axiom.Extensionality.
Require Import ZF.Axiom.Union.
Require Import ZF.Class.Small.
Require Import ZF.Core.Leq.
Require Import ZF.Core.Or.
Require Import ZF.Core.Union.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Pair.

(* It is useful to define the predicate underlying the union axiom.             *)
Definition UnionPred (a:U) : U -> Prop := fun x =>
  exists y, x :< y /\ y :< a.

(* The union predicate of the set a is small.                                   *)
Proposition UnionSmall : forall (a:U),
  Small (UnionPred a).
Proof.
  apply ZF.Axiom.Union.Union.
Qed.

(* We consider the set defined by the union predicate of the set a.             *)
Definition union (a:U) : U
  := fromClass (UnionPred a) (UnionSmall a).

(* Notation ":U( a )" := (union a)                                              *)
Global Instance SetUnion : Union U := { union := union }.

(* The union of two sets.                                                       *)
Definition union2 (a b:U) : U := :U( :{a,b}: ).

(* Notation "a :\/: b" := (union a b)                                           *)
Global Instance SetOr : Or U := { or := union2 }.

(* Characterisation of the elements of the union set of a.                      *)
Proposition UnionSetCharac : forall (a:U),
  forall x, x :< :U(a) <-> exists y, x :< y /\ y :< a.
Proof.
  unfold union. intros a. apply FromClassCharac.
Qed.

(* Characterisation of the elements of the union of two sets.                   *)
Proposition UnionCharac : forall (a b:U),
  forall x, x :< a:\/:b <-> x :< a \/ x :< b.
Proof.
  intros a b x. unfold union. split.
  - intros H. apply UnionSetCharac in H. destruct H as [y [H1 H2]].
    apply PairCharac in H2. destruct H2 as [H2|H3]; subst.
    + left. apply H1.
    + right. apply H1.
  - intros [H1|H1].
    + apply UnionSetCharac. exists a. split.
      * apply H1.
      * apply PairInL.
    + apply UnionSetCharac. exists b. split.
      * apply H1.
      * apply PairInR.
Qed.

(* The union of two sets is commutative.                                        *)
Proposition UnionComm : forall (a b:U), a:\/:b = b:\/:a.
Proof.
  intros a b. apply Extensionality. intros x. split;
  intros H1; apply UnionCharac; apply UnionCharac in H1;
  destruct H1 as [H1|H1]; auto.
Qed.

(* The union of two sets is associative.                                        *)
Proposition UnionAssoc : forall (a b c:U), (a:\/:b):\/:c = a:\/:(b:\/:c).
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1;
  apply UnionCharac in H1; apply UnionCharac; destruct H1 as [H1|H1].
  - apply UnionCharac in H1. destruct H1 as [H1|H1].
    + left. apply H1.
    + right. apply UnionCharac. left. apply H1.
  - right. apply UnionCharac. right. apply H1.
  - left. apply UnionCharac. left. apply H1.
  - apply UnionCharac in H1. destruct H1 as [H1|H1].
    + left. apply UnionCharac. right. apply H1.
    + right. apply H1.
Qed.

(* Union is compatible with inclusion.                                          *)
Proposition UnionInclCompat : forall (a b c d:U),
  a :<=: b -> c :<=: d -> a:\/:c :<=: b:\/:d.
Proof.
  intros a b c d H1 H2 x H3. apply UnionCharac in H3.
  destruct H3 as [H3|H3]; apply UnionCharac.
  - left. apply H1. assumption.
  - right. apply H2. assumption.
Qed.

(* Union is left-compatible with inclusion.                                     *)
Proposition UnionInclCompatL : forall (a b c:U),
  a :<=: b -> a:\/:c :<=: b:\/:c.
Proof.
  intros a b c H1. apply UnionInclCompat.
  - assumption.
  - apply InclRefl.
Qed.

(* Union is right-compatible with inclusion.                                    *)
Proposition UnionInclCompatR : forall (a b c:U),
  a :<=: b -> c:\/:a :<=: c:\/:b.
Proof.
  intros a b c H1. apply UnionInclCompat.
  - apply InclRefl.
  - assumption.
Qed.

Proposition UnionEqualIncl : forall (a b:U),
  b = a :\/: b <-> a :<=: b.
Proof.
  intros a b. split; intros H1.
  - intros x H2. rewrite H1. apply UnionCharac. left. apply H2.
  - apply Extensionality. intros x. split; intros H2.
    + apply UnionCharac. right. apply H2.
    + apply UnionCharac in H2. destruct H2 as [H2|H2].
      * apply H1, H2.
      * apply H2.
Qed.

Proposition UnionInclL : forall (a b:U), a :<=: a:\/:b.
Proof.
  intros a b x H1. apply UnionCharac. left. apply H1.
Qed.

Proposition UnionInclR : forall (a b:U), b :<=: a:\/:b.
Proof.
  intros a b x H1. apply UnionCharac. right. apply H1.
Qed.

