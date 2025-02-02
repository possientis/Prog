Require Import ZF.Axiom.Classic.
Require Import ZF.Axiom.Extensionality.
Require Import ZF.Class.Empty.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Singleton.
Export ZF.Core.Zero.

(* We consider the set defined by the small class Empty                         *)
Definition empty : U := fromClass :0: EmptyIsSmall.

(* Notation ":0:" := emptySet                                                   *)
Global Instance SetZero : Zero U := { zero := empty }.

(* Characterisation of the elements of the empty set.                           *)
Proposition EmptyCharac : forall x, x :< :0: <-> False.
Proof.
  apply FromClassCharac.
Qed.

(* The empty set has no element.                                                *)
Proposition EmptySetEmpty : forall x, ~ x :< :0:.
Proof.
  intros x H1. apply EmptyCharac in H1. apply H1.
Qed.

(* If a set is not empty, then it has an element.                               *)
Proposition NotEmptyHasElement : forall (a:U),
  a <> :0: <-> exists x, x :< a.
Proof.
  intros a. split; intros H1.
  - apply NotForAllNot. intros H2. apply H1, Extensionality.
    intros x. split; intros H3.
    + apply EmptyCharac, (H2 x), H3.
    + apply EmptyCharac in H3. contradiction.
  - destruct H1 as [x H1]. intros H2. rewrite H2 in H1.
    apply EmptyCharac in H1. apply H1.
Qed.

Proposition IfEmptyThenEmpty : forall (a:U),
  (forall x, ~ x :< a) -> a = :0:.
Proof.
  intros a Ha. apply Extensionality. intros x. split; intros H1.
  - apply (Ha x) in H1. contradiction.
  - apply EmptyCharac in H1. contradiction.
Qed.

(* A pair is never equal to the empty set.                                      *)
Proposition PairNotEmpty : forall (a b:U), :{a,b}: <> :0:.
Proof.
  intros a b H1. assert (a :< :0:) as H2. { rewrite <- H1. apply PairInL. }
  apply EmptyCharac in H2. contradiction.
Qed.

(* The empty set is not an ordered pair                                         *)
Proposition OrdPairNotEmpty : forall (x y:U), :(x,y): <> :0:.
Proof.
  intros x y H1. apply DoubleInclusion in H1. destruct H1 as [H1 _].
  apply EmptySetEmpty with :{x}:. apply H1, PairInL.
Qed.

Proposition SingletonNotEmpty : forall a, :{a}: <> :0:.
Proof.
  intros a. apply PairNotEmpty.
Qed.
