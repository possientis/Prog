Declare Scope ZF_Set_Pair_scope.
Open    Scope ZF_Set_Pair_scope.

Require Import ZF.Axiom.Pairing.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.

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
  := fromClass (PairPred a b) (PairSmall a b).

Notation ":{ a , b }:" := (pairSet a b)
  (at level 1, no associativity) : ZF_Set_Pair_scope.

(* Characterisation of the elements of {a,b}.                                   *)
Proposition PairCharac : forall (a b:U),
  forall x, x :< :{a,b}: <-> x = a \/ x = b.
Proof.
  unfold pairSet. intros a b. apply FromClassCharac.
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
