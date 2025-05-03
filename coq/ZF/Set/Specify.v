Declare Scope ZF_Set_Specify_scope.
Open    Scope ZF_Set_Specify_scope.

Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.

(* Set comprehension (specification)  {x :< a | P x }.                          *)
Definition specify (P:Class) (a:U) : U := fromClass (toClass a :/\: P)
  (Inter2.IsSmallL (toClass a) P (SetIsSmall a)).

Notation ":{ a | P }:" := (specify P a)
  (at level 1, no associativity) : ZF_Set_Specify_scope.

(* Characterisation of the elements of { x :< a | P x}.                         *)
Proposition Charac : forall (P:Class) (a:U),
  forall x, x :< :{a | P}: <-> x :< a /\ P x.
Proof.
  intros P a. apply FromClass.Charac.
Qed.

(* Every element of the specification set of P and a is an element of a.        *)
Proposition InA : forall (P:Class) (a:U),
  forall x, x :< :{a | P}: -> x :< a.
Proof.
  intros P a x H1. apply Charac in H1. destruct H1 as [H1 _]. apply H1.
Qed.

(* Every element of the specification set of P and a lies in the class P.       *)
Proposition InP : forall (P:Class) (a:U),
  forall x, x :< :{a | P}: -> P x.
Proof.
  intros P a x H1. apply Charac in H1. destruct H1 as [_ H1]. apply H1.
Qed.

Proposition IsA : forall (P:Class) (a:U),
  toClass a :<=: P <-> :{a | P}: = a.
Proof.
  intros P a. split; intros H1.
  - apply DoubleInclusion. split; intros x H2.
    + apply InA with P. assumption.
    + apply Charac. split. 1: assumption. apply H1. assumption.
  - intros x H2. apply InP with a. rewrite H1. assumption.
Qed.

