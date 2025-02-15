Require Import ZF.Axiom.Define.
Require Import ZF.Axiom.Extensionality.
Require Import ZF.Class.
Require Import ZF.Class.Small.
Require Import ZF.Set.

(* Let us consider the predicate of the set potentially defined by a class P.   *)
Definition FromClassPred (P:Class) : U -> Prop := fun a =>
  forall x, x :< a <-> P x.

(* If a class is a small, its set predicate is satisfied by at least one set.   *)
Proposition FromClassExists : forall (P:Class),
  Small P -> Exists (FromClassPred P).
Proof.
  intros P H. apply H.
Qed.

(* The set predicate of a class is always satisfied by at most one set.         *)
Proposition FromClassUnique : forall (P:Class), Unique (FromClassPred P).
Proof.
  intros P. unfold Unique, FromClassPred. intros a b Ha Hb.
  apply ClassEquivSetEqual. apply ClassEquivTran with P.
  - intros x. apply Ha.
  - apply ClassEquivSym. intros x. apply Hb.
Qed.

(* If a class is small, we can define the set to which it corresponds .         *)
Definition fromClass (P :Class) (q:Small P) : U
  := define (FromClassPred P) (FromClassExists P q) (FromClassUnique P).

(* The set associated with a small class satisfies its set predicate.           *)
Proposition FromClassSatisfy : forall (P:Class) (q:Small P),
  FromClassPred P (fromClass P q).
Proof.
  intros P q. unfold fromClass. apply DefineSatisfy.
Qed.

(* Characterisation of the elements of the set associated with a small class.   *)
Proposition FromClassCharac : forall (P:Class) (q:Small P),
  forall x, x :< (fromClass P q) <-> P x.
Proof.
  apply FromClassSatisfy.
Qed.

(* The set defined by a small class does not depend on the proof being used.    *)
Proposition FromClassProofIrrelevant : forall (P:Class) (q q':Small P),
  fromClass P q = fromClass P q'.
Proof.
  intros P q q'. unfold fromClass. apply DefineProof.
Qed.

(* The set associated with the class associated with a set is the set itself.   *)
Proposition FromToClass : forall (a:U),
  fromClass (toClass a) (SetIsSmall a) = a.
Proof.
  intro a. apply ClassEquivSetEqual. intros x. apply FromClassCharac.
Qed.

(* The class associated with the set associated with a small class is the class.*)
Proposition ToFromClass : forall (P:Class) (q:Small P),
  toClass (fromClass P q) :~: P.
Proof.
  intros P q x. apply FromClassCharac.
Qed.
