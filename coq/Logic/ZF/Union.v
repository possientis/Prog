Declare Scope ZF_Union_scope.
Open    Scope ZF_Union_scope.

Require Import Logic.ZF.Core.
Require Import Logic.ZF.Define.
Require Import Logic.ZF.Extensionality.
Require Import Logic.ZF.Pairing.

(* Given a set a, there exists a set b whose elements are the elements of all   *)
(* the elements of a. More formally:                                            *)
Axiom Union : forall a, exists b,
  forall x, x :< b <-> exists y, x :< y /\ y :< a.

(* It is useful to define the predicate underlying the union axiom.             *)
Definition UnionPred (a:U) : U -> Prop := fun b =>
  forall x, x :< b <-> exists y, x :< y /\ y :< a.

(* The union predicate of the set a is satisfied by at least one set.           *)
Proposition UnionExists : forall (a:U), Exists (UnionPred a).
Proof.
  intros a. apply Union.
Qed.

(* The union predicate of the set a is satisfied by no more than one set.       *)
Proposition UnionUnique : forall (a:U), Unique (UnionPred a).
Proof.
  intros a. unfold Unique. apply SameCharacEqual.
Qed.

(* We consider the set defined by the union predicate of the set a.             *)
Definition unionSet (a:U) : U
  := define (UnionPred a) (UnionExists a) (UnionUnique a).

Notation "U( a )" := (unionSet a)
  (at level 0, no associativity) : ZF_Union_scope.

(* The union of two sets.                                                       *)
Definition union (a b:U) : U := U( :{a,b}: ).

Notation "a :\/: b" := (union a b)
  (at level 4, left associativity) : ZF_Union_scope.

(* The union set of a satisfies the union predicate of a.                       *)
Proposition UnionSatisfy : forall (a:U), UnionPred a U(a).
Proof.
  intros a. unfold unionSet. apply DefineSatisfy.
Qed.

(* Characterisation of the elements of the union set of a.                      *)
Proposition UnionSetCharac : forall (a:U),
  forall x, x :< U(a) <-> exists y, x :< y /\ y :< a.
Proof.
  apply UnionSatisfy.
Qed.

(* Characterisation of the elements of the union of two sets.                   *)
Proposition UnionCharac : forall (a b:U),
  forall x, x :< (a:\/:b) <-> x :< a \/ x :< b.
Proof.
  intros a b x. unfold union. split.
  - intros H. apply UnionSetCharac in H. destruct H as [y [H1 H2]].
    apply PairCharac in H2. destruct H2 as [H2|H3]; subst.
    + left. apply H1.
    + right. apply H1.
  - intros [H1|H1].
    + apply UnionSetCharac. exists a. split.
      * apply H1.
      * apply PairIn1.
    + apply UnionSetCharac. exists b. split.
      * apply H1.
      * apply PairIn2.
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
