Require Import List.

Require Import Core.Set.

Definition inListOf (x xs:set) : Prop := In x (toList xs).
