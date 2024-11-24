Require Import ZF.Axiom.Core.
Require Import ZF.Set.OrdPair.

(* A relation is a set of ordered pairs.                                        *)
Definition Relation (a:U) : Prop :=
  forall x, x :< a -> exists y, exists z, x = :(y,z):.

