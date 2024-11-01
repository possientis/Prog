Declare Scope ZF_Pairing_scope.
Open    Scope ZF_Pairing_scope.

Require Import Logic.ZF.Core.
Require Import Logic.ZF.Define.
Require Import Logic.ZF.Extensionality.

(* Given two sets a and b, there exists a set c whose elements are a and b.     *)
Axiom Pairing : forall a b, exists c, forall x, x :< c <-> x = a \/ x = b.

(* It is useful to define the predicate underlying the pairing axiom.           *)
Definition PairPred (a b:U) : U -> Prop := fun c =>
  forall x, x :< c <-> x = a \/ x = b.

(* The pairing predicate of a and b is satisfied by at least one set.           *)
Proposition PairExists : forall (a b:U), Exists (PairPred a b).
Proof.
  intros a b. apply Pairing.
Qed.

(* The pairing predicate of a and b is satisfied by no more than one set.       *)
Proposition PairUnique : forall (a b:U), Unique (PairPred a b).
Proof.
  intros a b. unfold Unique. apply SameCharacEqual.
Qed.

(* We consider the set defined by the pairing predicate of a and b.             *)
Definition pairSet (a b:U) : U
  := define (PairPred a b) (PairExists a b) (PairUnique a b).

Notation ":{ a , b }:" := (pairSet a b)
  (at level 1, no associativity) : ZF_Pairing_scope.

(* The pair {a,b} satisfies the pairing predicate of a and b.                   *)
Proposition PairSatisfy : forall (a b:U), PairPred a b :{a,b}:.
Proof.
  intros a b. unfold pairSet. apply DefineSatisfy.
Qed.

(* Characterisation of the elements of {a,b}.                                   *)
Proposition PairCharac : forall (a b:U),
  forall x, x :< :{a,b}: <-> x = a \/ x = b.
Proof.
  apply PairSatisfy.
Qed.

(* If a set x is equal to the set a, then it belongs to the set {a,b}.          *)
Proposition PairEqualAIn : forall (a b:U),
  forall x, x = a -> x :< :{a,b}:.
Proof.
  intros a b x Hx. apply PairCharac. left. apply Hx.
Qed.

(* If a set x is equal to the set b, then it belongs to the set {a,b}.          *)
Proposition PairEqualBIn : forall (a b:U),
  forall x, x = b -> x :< :{a,b}:.
Proof.
  intros a b x Hx. apply PairCharac. right. apply Hx.
Qed.

(* The set a is an element of the set {a,b}.                                    *)
Proposition PairAIn : forall (a b:U), a :< :{a,b}:.
Proof.
  intros a b. apply PairEqualAIn. reflexivity.
Qed.

(* The set b is an element of the set {a,b}.                                    *)
Proposition PairBIn : forall (a b:U), b :< :{a,b}:.
Proof.
  intros a b. apply PairEqualBIn. reflexivity.
Qed.
