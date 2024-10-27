Declare Scope ZF_Singleton_scope.
Open    Scope ZF_Singleton_scope.

Require Import Logic.ZF.Core.
Require Import Logic.ZF.Pairing.

Definition singleton (a:U) : U := {a,a}.

(* Unfortunately, it appears we cannot use the notation '{a}' here.             *)
Notation "[ a ]" := (singleton a)
  (at level 1, no associativity) : ZF_Singleton_scope.

(* Characterisation of the elements of [a].                                     *)
Proposition SingleCharac : forall (a:U),
  forall x, x :< [a] <-> x = a.
Proof.
  intros a x. split.
  - intros Hx. apply PairCharac in Hx. destruct Hx as [Hx|Hx]; apply Hx.
  - intros Hx. apply PairCharac. left. apply Hx.
Qed.

(* An element of [a] is equal to a                                              *)
Proposition SingleInEqual : forall (a:U),
  forall x, x :< [a] -> x = a.
Proof.
  intros a x. apply SingleCharac.
Qed.

(* If a set x is equal to the set a, then it belongs to the singleton [a].      *)
Proposition SingleEqualIn : forall (a:U),
  forall x, x = a -> x :< [a].
Proof.
  intros a x Hx. apply SingleCharac, Hx.
Qed.

(* The set a is an element of the singleton set [a].                            *)
Proposition SingleIn : forall (a:U), a :< [a].
Proof.
  intros a. apply SingleEqualIn. reflexivity.
Qed.
