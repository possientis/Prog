Declare Scope ZF_Core_Equiv_scope.
Open    Scope ZF_Core_Equiv_scope.

Class Equiv (v:Type) := { equiv : v -> v -> Prop }.

Notation "x :~: y" := (equiv x y)
  (at level 50, no associativity) : ZF_Core_Equiv_scope.

Notation "x :<>: y" := (~ equiv x y)
  (at level 50, no associativity) : ZF_Core_Equiv_scope.
