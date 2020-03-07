Require Import Core.Set.
Require Import Core.Equal.

Definition functional (p:set -> set -> Prop) : Prop :=
    forall (x y y':set), p x y -> p x y' -> y == y'.
