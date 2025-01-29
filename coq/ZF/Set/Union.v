Require Import ZF.Class.
Require Import ZF.Class.Small.
Require Import ZF.Class.Union.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.
Export ZF.Core.Union.

(* We consider the set defined by the union predicate of the set a.             *)
Definition union (a:U) : U := fromClass :U(toClass a)
  (UnionIsSmall (toClass a) (SetIsSmall a)).

(* Notation ":U( a )" := (union a)                                              *)
Global Instance SetUnion : Union U := { union := union }.

(* Characterisation of the elements of the union set of a.                      *)
Proposition UnionCharac : forall (a:U),
  forall x, x :< :U(a) <-> exists y, x :< y /\ y :< a.
Proof.
  intros a. apply FromClassCharac.
Qed.
