Require Import ZF.Axiom.Define.
Require Import ZF.Axiom.Extensionality.
Require Import ZF.Class.Core.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.

(* Let us consider the predicate of the set potentially defined by a class P.   *)
Definition IsSetFromClass (P:Class) : U -> Prop := fun a =>
  forall x, x :< a <-> P x.

(* If a class is a small, its set predicate is satisfied by at least one set.   *)
Proposition Exists : forall (P:Class),
  Small P -> Define.Exists (IsSetFromClass P).
Proof.
  intros P H. apply H.
Qed.

(* The set predicate of a class is always satisfied by at most one set.         *)
Proposition Unique : forall (P:Class), Define.Unique (IsSetFromClass P).
Proof.
  intros P a b Ha Hb.
  apply EqualToClass. apply EquivTran with P.
  - intros x. apply Ha.
  - apply EquivSym. intros x. apply Hb.
Qed.

(* If a class is small, we can define the set to which it corresponds .         *)
Definition fromClass (P :Class) (q:Small P) : U
  := define (IsSetFromClass P) (Exists P q) (Unique P).

(* The set associated with a small class satisfies its set predicate.           *)
Proposition Satisfy : forall (P:Class) (q:Small P),
  IsSetFromClass P (fromClass P q).
Proof.
  intros P q. unfold fromClass. apply DefineSatisfy.
Qed.

(* Characterisation of the elements of the set associated with a small class.   *)
Proposition Charac : forall (P:Class) (q:Small P),
  forall x, x :< (fromClass P q) <-> P x.
Proof.
  apply Satisfy.
Qed.

(* The set defined by a small class does not depend on the proof being used.    *)
Proposition ProofIrrelevant : forall (P:Class) (q q':Small P),
  fromClass P q = fromClass P q'.
Proof.
  intros P q q'. unfold fromClass. apply DefineProof.
Qed.

(* The set associated with the class associated with a set is the set itself.   *)
Proposition FromToClass : forall (a:U),
  fromClass (toClass a) (SetIsSmall a) = a.
Proof.
  intro a. apply EqualToClass. intros x. apply Charac.
Qed.

(* The class associated with the set associated with a small class is the class.*)
Proposition ToFromClass : forall (P:Class) (q:Small P),
  toClass (fromClass P q) :~: P.
Proof.
  intros P q x. apply Charac.
Qed.
