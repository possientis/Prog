Require Import set.
Require Import belong.

(************************************************************************)
(*                            The union axiom                           *)
(************************************************************************)

Axiom union_axiom : forall a:set, exists b:set,
  forall x:set, x:b <-> exists y:set, x:y /\ y:a.


