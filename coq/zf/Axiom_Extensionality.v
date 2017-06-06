Require Import set.
Require Import subset.

(************************************************************************)
(*                       The extensionality axiom                       *)
(************************************************************************)

Axiom extensionality : forall a b:set, 
  subset a b -> subset b a -> a = b.


