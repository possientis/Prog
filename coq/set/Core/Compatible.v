Require Import Core.Set.
Require Import Core.Equal.

Definition compatible (P:set -> Prop) : Prop :=
    forall (x y:set), x == y -> P x -> P y.
