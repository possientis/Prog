Declare Scope ZF_Pairing_scope.
Open    Scope ZF_Pairing_scope.

Require Import Logic.ZF.Class.
Require Import Logic.ZF.Core.
Require Import Logic.ZF.Empty.
Require Import Logic.ZF.Extensionality.

(* Given two sets a and b, there exists a set c whose elements are a and b.     *)
Axiom Pairing : forall a b, exists c, forall x, x :< c <-> x = a \/ x = b.

(* It is useful to define the predicate underlying the pairing axiom.           *)
Definition PairPred (a b:U) : U -> Prop := fun x =>
  x = a \/ x = b.

(* The pairing predicate of the sets a and b is small.                          *)
Proposition PairSmall : forall (a b:U),
  Small (PairPred a b).
Proof.
  apply Pairing.
Qed.

(* We consider the set defined by the pairing predicate of a and b.             *)
Definition pairSet (a b:U) : U
  := toSet (PairPred a b) (PairSmall a b).

Notation ":{ a , b }:" := (pairSet a b)
  (at level 1, no associativity) : ZF_Pairing_scope.

(* Characterisation of the elements of {a,b}.                                   *)
Proposition PairCharac : forall (a b:U),
  forall x, x :< :{a,b}: <-> x = a \/ x = b.
Proof.
  unfold pairSet. intros a b. apply ClassCharac.
Qed.

(* If a set x is equal to the set a, then it belongs to the set {a,b}.          *)
Proposition PairEqualIn1 : forall (a b:U),
  forall x, x = a -> x :< :{a,b}:.
Proof.
  intros a b x Hx. apply PairCharac. left. apply Hx.
Qed.

(* If a set x is equal to the set b, then it belongs to the set {a,b}.          *)
Proposition PairEqualIn2 : forall (a b:U),
  forall x, x = b -> x :< :{a,b}:.
Proof.
  intros a b x Hx. apply PairCharac. right. apply Hx.
Qed.

(* The set a is an element of the set {a,b}.                                    *)
Proposition PairIn1 : forall (a b:U), a :< :{a,b}:.
Proof.
  intros a b. apply PairEqualIn1. reflexivity.
Qed.

(* The set b is an element of the set {a,b}.                                    *)
Proposition PairIn2 : forall (a b:U), b :< :{a,b}:.
Proof.
  intros a b. apply PairEqualIn2. reflexivity.
Qed.

(* A pair is never equal to the empty set.                                      *)
Proposition PairNotEmpty : forall (a b:U), ~ :{a,b}: = :0:.
Proof.
  intros a b Hab. assert (a :< :0:) as H1. { rewrite <- Hab. apply PairIn1. }
  apply EmptyCharac in H1. apply H1.
Qed.
