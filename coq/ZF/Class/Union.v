Declare Scope ZF_Class_Union_scope.
Open    Scope ZF_Class_Union_scope.

Require Import ZF.Class.
Require Import ZF.Core.Or.
Require Import ZF.Set.

(* The union class of a class.                                                  *)
Definition unionClass (P:Class) : Class := fun x =>
  exists y, x :< y /\ P y.

Notation ":U( P )" := (unionClass P)
  (at level 0, no associativity) : ZF_Class_Union_scope.

(* The union of two classes.                                                    *)
Definition union (P Q:Class) : Class := fun x => P x \/ Q x.

(* Notation "P :\/: P" := (union P Q)                                           *)
Global Instance ClassOr : Or Class := { or := union }.
