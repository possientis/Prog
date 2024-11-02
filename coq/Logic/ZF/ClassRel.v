Declare Scope ZF_ClassRel_scope.
Open    Scope ZF_ClassRel_scope.

Require Import Logic.ZF.Class.
Require Import Logic.ZF.Core.

(* A class relation is simply a binary predicate on sets.                       *)
Definition ClassRel : Type := U -> U -> Prop.

(* Predicate expressing the fact that a class relation is functional.           *)
Definition Functional (F:ClassRel) : Prop :=
  forall x, forall y, forall z, F x y /\ F x z -> y = z.

(* Direct image of a set a by a class relation R.                               *)
Definition Image (R:ClassRel) (a:U) : Class := fun y =>
  exists x, x :< a /\ R x y.

Notation "R [ a ]" := (Image R a)
  (at level 0, no associativity) : ZF_ClassRel_scope.
