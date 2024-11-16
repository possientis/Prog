Declare Scope ZF_Power_scope.
Open    Scope ZF_Power_scope.

Require Import ZF.Axiom.Core.
Require Import ZF.Axiom.Extensionality.
Require Import ZF.Class.Class.
Require Import ZF.Set.Include.

(* Given a set a, there exists a set b whose elements are the subsets of a.     *)
Axiom Power : forall a, exists b,
  forall x, x :< b <-> x :<=: a.

(* It is useful to define the predicate underlying the power axiom.             *)
Definition PowerPred (a:U) : U -> Prop := fun x => x :<=: a.

(* The power predicate of the set a is small.                                   *)
Proposition PowerSmall : forall (a:U),
  Small (PowerPred a).
Proof.
  apply Power.
Qed.

(* We consider the set defined by the power predicate of the set a.             *)
Definition powerSet (a:U) : U
  := toSet (PowerPred a) (PowerSmall a).

Notation ":P( a )" := (powerSet a)
  (at level 0, no associativity) : ZF_Power_scope.

(* Characterisation of the elements of the power set of a.                      *)
Proposition PowerCharac : forall (a:U),
  forall x, x :< :P(a) <-> x :<=: a.
Proof.
  unfold powerSet. intros a. apply ClassCharac.
Qed.
