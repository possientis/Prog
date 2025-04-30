Require Import ZF.Class.Core.
Require Import ZF.Class.Small.
Require Import ZF.Class.Union.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Export ZF.Notation.Union.

(* We consider the set defined by the union predicate of the set a.             *)
Definition union (a:U) : U := fromClass :U(toClass a)
  (IsSmall (toClass a) (SetIsSmall a)).

(* Notation ":U( a )" := (union a)                                              *)
Global Instance SetUnion : Union U := { union := union }.

(* Characterisation of the elements of the union set of a.                      *)
Proposition Charac : forall (a:U),
  forall x, x :< :U(a) <-> exists y, x :< y /\ y :< a.
Proof.
  intros a. apply FromClass.Charac.
Qed.

Proposition ToClass : forall (a:U),
  :U(toClass a) :~: toClass :U(a).
Proof.
  intros a x. split; intros H1.
  - destruct H1 as [y [H1 H2]]. apply Charac. exists y.
    split; assumption.
  - apply Charac in H1. destruct H1 as [y [H1 H2]]. exists y.
    split; assumption.
Qed.
