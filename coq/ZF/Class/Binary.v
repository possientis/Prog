Declare Scope ZF_Binary_scope.
Open    Scope ZF_Binary_scope.

Require Import ZF.Axiom.Core.
Require Import ZF.Class.Class.

(* A binary class is simply a binary predicate on sets.                         *)
Definition Binary : Type := U -> U -> Prop.

(* Predicate expressing the fact that a binary class is functional.             *)
Definition Functional (F:Binary) : Prop :=
  forall x, forall y, forall z, F x y -> F x z -> y = z.

(* Direct image of a set a by a binary class F.                                 *)
Definition Image (F:Binary) (a:U) : Class := fun y =>
  exists x, x :< a /\ F x y.

Notation "R [ a ]" := (Image R a)
  (at level 0, no associativity) : ZF_Binary_scope.
