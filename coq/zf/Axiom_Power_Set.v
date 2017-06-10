Require Import set.
Require Import belong.
Require Import subset.

(************************************************************************)
(*                         The power set axiom                          *)
(************************************************************************)

Axiom power_set : forall a:set, exists b:set,
  forall x:set, x:b <-> subset x a.


