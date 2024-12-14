Require Import ZF.Set.

(* Given two sets a and b, there exists a set c whose elements are a and b.     *)
Axiom Pairing : forall a b, exists c, forall x, x :< c <-> x = a \/ x = b.
