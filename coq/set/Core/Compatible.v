Require Import Core.Set.
Require Import Core.Equal.

Definition compatible (P:set -> Prop) : Prop :=
    forall (x x':set), x == x' -> P x -> P x'.

Definition compatible2 (P:set -> set -> Prop) : Prop :=
    forall (x x' y y':set), x == x' -> y == y' -> P x y -> P x' y'.
