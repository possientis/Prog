Require Import set.
Require Import belong.

(************************************************************************)
(*                          The pairing axiom                           *)
(************************************************************************)

Axiom pairing : forall a b:set, exists c:set,
  forall x:set, x:c <-> x = a \/ x = b. 
