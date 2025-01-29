Declare Scope ZF_Axiom_Specify_scope.
Open    Scope ZF_Axiom_Specify_scope.

Require Import ZF.Class.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Small.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.

(* Set comprehension (specification)  {x :< a | P x }.                          *)
Definition specify (P:Class) (a:U) : U := fromClass (toClass a :/\: P)
  (InterIsSmallL (toClass a) P (SetIsSmall a)).

Notation ":{ a | P }:" := (specify P a)
  (at level 1, no associativity) : ZF_Axiom_Specify_scope.

(* Characterisation of the elements of { x :< a | P x}.                         *)
Proposition SpecifyCharac : forall (P:Class) (a:U),
  forall x, x :< :{a | P}: <-> x :< a /\ P x.
Proof.
  intros P a. apply FromClassCharac.
Qed.

(* Every element of the specification set of P and a is an element of a.        *)
Proposition SpecifyInInA : forall (P:Class) (a:U),
  forall x, x :< :{a | P}: -> x :< a.
Proof.
  intros P a x H1. apply SpecifyCharac in H1. destruct H1 as [H1 _]. apply H1.
Qed.

(* Every element of the specification set of P and a lies in the class P.       *)
Proposition SpecifyInP : forall (P:Class) (a:U),
  forall x, x :< :{a | P}: -> P x.
Proof.
  intros P a x H1. apply SpecifyCharac in H1. destruct H1 as [_ H1]. apply H1.
Qed.
