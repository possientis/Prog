Require Import ZF.Set.

(* If two sets have the same elements, then they are equal                      *)
Axiom Extensionality : forall a b, (forall x, x :< a <-> x :< b) -> a = b.
