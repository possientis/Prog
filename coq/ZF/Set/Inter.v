Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Small.
Require Import ZF.Class.Inter.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Single.

Export ZF.Notation.Inter.

(* We consider the set defined by the intersection of a.                        *)
Definition inter (a:U) : U := fromClass :I(toClass a) (IsSmall (toClass a)).

(* Notation ":I( a )" := (inter a)                                              *)
Global Instance SetInter : Inter U := { inter := inter }.

(* Characterisation of the elements of the intersection of a.                   *)
Proposition Charac : forall (a x y:U),
  x :< :I(a) -> y :< a -> x :< y.
Proof.
  intros a x y H1 H2.
  apply FromClass.Charac in H1. destruct H1 as [H1 _]. apply H1. assumption.
Qed.

Proposition CharacRev : forall (a x:U), a <> :0: ->
  (forall y, y :< a -> x :< y) -> x :< :I(a).
Proof.
  intros a x H1 H2. apply FromClass.Charac. split.
  - intros y H3. apply H2. assumption.
  - apply Empty.HasElem in H1. assumption.
Qed.

(* The inter' of the class is the class of the intersection.                    *)
Proposition ToClass' : forall (a:U), a <> :0: ->
  inter' (toClass a) :~: toClass :I(a).
Proof.
  intros a H1 x. split; intros H2.
  - apply CharacRev; assumption.
  - intros y H3. apply Charac with a; assumption.
Qed.

(* The intersection of the class is the class of the intersection.              *)
Proposition ToClass : forall (a:U),
  :I(toClass a) :~: toClass :I(a).
Proof.
  intros a x. split; intros H1.
  - apply FromClass.Charac. assumption.
  - apply FromClass.Charac in H1. assumption.
Qed.

(* The intersection of the empty set is the empty set.                          *)
Proposition IsZero : :I(:0:) = :0:.
Proof.
  apply DoubleInclusion. split; intros x H1.
  - apply FromClass.Charac in H1. apply (Inter.EquivCompat :0:) in H1.
    + apply IsZero in H1. contradiction.
    + apply Equiv.Sym, Empty.ToClass.
  - apply Empty.Charac in H1. contradiction.
Qed.

(* The intersection of a singleton is the element of the singleton.             *)
Proposition WhenSingleton : forall (a:U),
  :I(:{a}:) = a.
Proof.
  intros a. apply DoubleInclusion. split; intros x H1.
  - apply Charac with :{a}:. 1: assumption. apply Single.IsIn.
  - apply CharacRev.
    + apply SingletonIsNotEmpty.
    + intros y H2. apply Single.Charac in H2. subst. assumption.
Qed.

