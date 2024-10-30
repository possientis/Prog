Require Import Logic.ZF.Core.
Require Import Logic.ZF.Define.
Require Import Logic.ZF.Extensionality.

(* A class is simply a predicate on sets.                                       *)
Definition Class : Type := U -> Prop.

(* Predicate on classes, determining whether a class is actually a set.         *)
Definition Small (P:Class) : Prop := exists a, forall x, x :< a <-> P x.

(* Predicate on classes, determining whether a class is strict.                 *)
Definition Strict (P:Class) : Prop := ~Small P.

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
  := Define (ClassPred P) (ClassExists P q) (ClassUnique P).

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

(* Every element of the set associated with a small class satisfies the class.  *)
Proposition ClassInP : forall (P:Class) (q:Small P),
  forall x, x :< (toSet P q) -> P x.
Proof.
  apply ClassCharac.
Qed.

(* Every set which satisfies a small class is an element of its associated set. *)
Proposition ClassPIn : forall (P:Class) (q:Small P),
  forall x, P x -> x :< (toSet P q).
Proof.
  apply ClassCharac.
Qed.

(* The set defined by a small class does not depend on the proof being used.    *)
Proposition ClassProof : forall (P:Class) (q q':Small P),
  toSet P q = toSet P q'.
Proof.
  intros P q q'. unfold toSet. apply DefineProof.
Qed.

(* A set can be viewed as a class.                                              *)
Definition fromSet (a:U) : Class := fun x => x :< a.

(* The class associated with a set is small                                     *)
Proposition fromSetSmall : forall (a:U), Small (fromSet a).
Proof.
  intros. unfold Small, fromSet. exists a. intros x. split; auto.
Qed.

(* The set associated with the class associated with a set is the set itself.   *)
Proposition toSetFromSet : forall (a:U),
  toSet (fromSet a) (fromSetSmall a) = a.
Proof.
  intro a. apply SameCharacEqual with (fromSet a).
  - apply ClassCharac.
  - unfold fromSet. intros x. split; auto.
Qed.

(* The class associated with the set associated with a small class is the class.*)
Proposition fromSetToSet : forall (P:Class) (q:Small P) (x:U),
  fromSet (toSet P q) x <-> P x.
Proof.
  intros P q x. unfold fromSet. apply ClassCharac.
Qed.

