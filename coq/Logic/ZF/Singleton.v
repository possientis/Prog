Declare Scope ZF_Singleton_scope.
Open    Scope ZF_Singleton_scope.

Require Import Logic.ZF.Core.
Require Import Logic.ZF.Empty.
Require Import Logic.ZF.Pairing.

(* The singleton set {a} is defined as the pair {a,a}.                          *)
Definition singleton (a:U) : U := :{a,a}:.

Notation ":{ a }:" := (singleton a)
  (at level 1, no associativity) : ZF_Singleton_scope.

(* Characterisation of the elements of {a}.                                     *)
Proposition SingleCharac : forall (a:U),
  forall x, x :< :{a}: <-> x = a.
Proof.
  intros a x. split.
  - intros Hx. apply PairCharac in Hx. destruct Hx as [Hx|Hx]; apply Hx.
  - intros Hx. apply PairCharac. left. apply Hx.
Qed.

(* The set a is an element of the singleton set [a].                            *)
Proposition SingleIn : forall a, a :< :{a}:.
Proof.
  intros a. apply SingleCharac. reflexivity.
Qed.

Proposition SingleEqualSingle : forall a b, :{a}: = :{b}: -> a = b.
Proof.
  intros a b Hab. apply SingleCharac. rewrite <- Hab.
  apply SingleCharac. reflexivity.
Qed.

Proposition SingleNotEmpty : forall a, ~ :{a}: = :0:.
Proof.
  intros a Ha. assert (a :< :0:) as H1. { rewrite <- Ha. apply SingleIn. }
  apply EmptyCharac in H1. apply H1.
Qed.
