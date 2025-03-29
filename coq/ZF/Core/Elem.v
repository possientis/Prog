Declare Scope ZF_Core_Elem_scope.
Open    Scope ZF_Core_Elem_scope.

Class Elem (v w:Type) := { elem : v -> w -> Prop }.

Notation "x :< y" := (elem x y)
  (at level 20, no associativity) : ZF_Core_Elem_scope.


