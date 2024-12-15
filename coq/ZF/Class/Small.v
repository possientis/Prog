Require Import ZF.Axiom.Define.
Require Import ZF.Axiom.Extensionality.
Require Import ZF.Class.
Require Import ZF.Core.Equal.
Require Import ZF.Core.Equiv.
Require Import ZF.Set.

(* Predicate on classes, stating that a class is actually a set.                *)
Definition Small (P:Class) : Prop := exists a, forall x, x :< a <-> P x.

(* Predicate on classes, determining whether a class is proper.                 *)
Definition Proper (P:Class) : Prop := ~Small P.

(* Let us consider the predicate of the set potentially defined by a class P.   *)
Definition ClassPred (P:Class) : U -> Prop := fun a =>
  forall x, x :< a <-> P x.

(* If a class is a small, its set predicate is satisfied by at least one set.   *)
Proposition ClassExists : forall (P:Class),
  Small P -> Exists (ClassPred P).
Proof.
  intros P H. apply H.
Qed.

(* The set predicate of a class is always satisfied by at most one set.         *)
Proposition ClassUnique : forall (P:Class), Unique (ClassPred P).
Proof.
  intros P. unfold Unique. apply SameCharacEqual.
Qed.

(* If a class is small, we can define the set to which it corresponds .         *)
Definition toSet (P :Class) (q:Small P) : U
  := define (ClassPred P) (ClassExists P q) (ClassUnique P).

(* The set associated with a small class satisfies its set predicate.           *)
Proposition ClassSatisfy : forall (P:Class) (q:Small P),
  ClassPred P (toSet P q).
Proof.
  intros P q. unfold toSet. apply DefineSatisfy.
Qed.

(* Characterisation of the elements of the set associated with a small class.   *)
Proposition ClassCharac : forall (P:Class) (q:Small P),
  forall x, x :< (toSet P q) <-> P x.
Proof.
  apply ClassSatisfy.
Qed.

(* The set defined by a small class does not depend on the proof being used.    *)
Proposition ClassProof : forall (P:Class) (q q':Small P),
  toSet P q = toSet P q'.
Proof.
  intros P q q'. unfold toSet. apply DefineProof.
Qed.

(* The class associated with a set is small                                     *)
Proposition ToClassSmall : forall (a:U), Small (toClass a).
Proof.
  intros. unfold Small, toClass. exists a. intros x. split; auto.
Qed.

(* The set associated with the class associated with a set is the set itself.   *)
Proposition ToSetToClass : forall (a:U),
  toSet (toClass a) (ToClassSmall a) = a.
Proof.
  intro a. apply SameCharacEqual with (toClass a).
  - apply ClassCharac.
  - unfold toClass. intros x. split; auto.
Qed.

(* The class associated with the set associated with a small class is the class.*)
Proposition ToClassToSet : forall (P:Class) (q:Small P),
  toClass (toSet P q) == P.
Proof.
  intros P q. apply ClassEquivCharac. unfold toClass. apply ClassCharac.
Qed.

