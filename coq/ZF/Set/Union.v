Require Import ZF.Axiom.Union.
Require Import ZF.Class.Small.
Require Import ZF.Core.Union.
Require Import ZF.Set.
Require Import ZF.Set.FromClass.

(* It is useful to define the predicate underlying the union axiom.             *)
Definition UnionPred (a:U) : U -> Prop := fun x =>
  exists y, x :< y /\ y :< a.

(* The union predicate of the set a is small.                                   *)
Proposition UnionSmall : forall (a:U),
  Small (UnionPred a).
Proof.
  apply ZF.Axiom.Union.Union.
Qed.

(* We consider the set defined by the union predicate of the set a.             *)
Definition union (a:U) : U
  := fromClass (UnionPred a) (UnionSmall a).

(* Notation ":U( a )" := (union a)                                              *)
Global Instance SetUnion : Union U := { union := union }.

(* Characterisation of the elements of the union set of a.                      *)
Proposition UnionCharac : forall (a:U),
  forall x, x :< :U(a) <-> exists y, x :< y /\ y :< a.
Proof.
  unfold union. intros a. apply FromClassCharac.
Qed.
