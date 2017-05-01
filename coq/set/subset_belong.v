Require Import set.
Require Import subset.
Require Import belong.
Require Import equiv.

Proposition subset_belong: forall (a b:set),
  subset a b <-> forall (x:set), belong x a -> belong x b.
Proof.
  intros a b. split. intros Hab x Hxa.

Show.
