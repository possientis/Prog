Declare Scope ZF_Set_Pair_scope.
Open    Scope ZF_Set_Pair_scope.

Require Import ZF.Class.
Require Import ZF.Class.Pair.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.

(* We consider the set defined by the pairing predicate of a and b.             *)
Definition pair (a b:U) : U := fromClass (Class.Pair.pair a b)
  (PairIsSmall a b).

Notation ":{ a , b }:" := (pair a b)
  (at level 1, no associativity) : ZF_Set_Pair_scope.

(* Characterisation of the elements of {a,b}.                                   *)
Proposition PairCharac : forall (a b:U),
  forall x, x :< :{a,b}: <-> x = a \/ x = b.
Proof.
  intros a b. apply FromClassCharac.
Qed.

(* If a set x is equal to the set a, then it belongs to the set {a,b}.          *)
Proposition PairEqualInL : forall (a b:U),
  forall x, x = a -> x :< :{a,b}:.
Proof.
  intros a b x Hx. apply PairCharac. left. apply Hx.
Qed.

(* If a set x is equal to the set b, then it belongs to the set {a,b}.          *)
Proposition PairEqualInR : forall (a b:U),
  forall x, x = b -> x :< :{a,b}:.
Proof.
  intros a b x Hx. apply PairCharac. right. apply Hx.
Qed.

(* The set a is an element of the set {a,b}.                                    *)
Proposition PairInL : forall (a b:U), a :< :{a,b}:.
Proof.
  intros a b. apply PairEqualInL. reflexivity.
Qed.

(* The set b is an element of the set {a,b}.                                    *)
Proposition PairInR : forall (a b:U), b :< :{a,b}:.
Proof.
  intros a b. apply PairEqualInR. reflexivity.
Qed.
