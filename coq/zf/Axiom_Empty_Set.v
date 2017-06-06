Require Import set.
Require Import belong.

(************************************************************************)
(*                      Existence of the empty set                      *)
(************************************************************************)

Axiom empty_set_exists : exists x:set, forall y:set, ~ belong y x.
