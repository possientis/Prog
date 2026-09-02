Require Import Logic.Set.Set.
Require Import Logic.Set.Equal.

Definition functional (p:set -> set -> Prop) : Prop :=
    forall (x y y':set), p x y -> p x y' -> y == y'.
