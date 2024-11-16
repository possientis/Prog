Require Import ZF.Axiom.Core.
Require Import ZF.Set.Include.

(* Given a set a, there exists a set b whose elements are the subsets of a.     *)
Axiom Power : forall a, exists b, forall x, x :< b <-> x :<=: a.


