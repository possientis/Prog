Require Import List.

Require Import Logic.Set.Set.

Definition inListOf (x xs:set) : Prop := In x (toList xs).
