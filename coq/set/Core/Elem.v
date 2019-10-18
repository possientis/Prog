Require Import Core.Set.
Require Import Core.Incl.

Notation "{ x }" := (Cons x Nil) : set_scope.

Open Scope set_scope.

Definition elem (x y:set) : Prop := incl {x} y. 

Notation "x :: y" := (elem x y) : set_scope.



