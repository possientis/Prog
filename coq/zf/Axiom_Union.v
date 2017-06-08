Require Import set.
Require Import belong.

(************************************************************************)
(*                            The union axiom                           *)
(************************************************************************)

Axiom union_axiom : forall a:set, exists b:set,
  forall x:set, belong x b <-> exists y:set, belong x y /\ belong y a.


