Declare Scope ZF_Set_Pair_scope.
Open    Scope ZF_Set_Pair_scope.

Require Import ZF.Class.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Pair.
Require Import ZF.Core.Leq.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.

(* We consider the set corresponding by the small class 'pair a b'.             *)
Definition pair (a b:U) : U := fromClass (Class.Pair.pair a b)
  (PairIsSmall a b).

Notation ":{ a , b }:" := (pair a b)
  (at level 1, no associativity) : ZF_Set_Pair_scope.

(* A set x belongs to {a,b} iff x = a or x = b.                                 *)
Proposition PairCharac : forall (a b:U),
  forall x, x :< :{a,b}: <-> x = a \/ x = b.
Proof.
  intros a b. apply FromClassCharac.
Qed.

(* The set a is an element of the set {a,b}.                                    *)
Proposition PairInL : forall (a b:U), a :< :{a,b}:.
Proof.
  intros a b. apply PairCharac. left. reflexivity.
Qed.

(* The set b is an element of the set {a,b}.                                    *)
Proposition PairInR : forall (a b:U), b :< :{a,b}:.
Proof.
  intros a b. apply PairCharac. right. reflexivity.
Qed.

Proposition PairToClassIncl : forall (A:Class) (a b:U),
  A a /\ A b <-> toClass :{a,b}: :<=: A.
Proof.
  intros A a b. split; intros H1.
  - destruct H1 as [H1 H2]. intros x H3. apply PairCharac in H3.
    destruct H3 as [H3|H3]; subst; assumption.
  - split; apply H1.
    + apply PairInL.
    + apply PairInR.
Qed.
