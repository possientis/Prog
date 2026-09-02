Require Import set.

(************************************************************************)
(*                      The skolemization axiom                         *)
(************************************************************************)

Axiom skolem: forall {P:set->Prop},
  (exists (x:set), P x) ->
  (forall (x y:set), P x -> P y -> x = y) -> { x:set | P x }.


