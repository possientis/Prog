Declare Scope ZF_Core_Equal_scope.
Open    Scope ZF_Core_Equal_scope.

Class Equal (v:Type) := { equal : v -> v -> Prop }.

Notation "x == y" := (equal x y)
  (at level 50, no associativity) : ZF_Core_Equal_scope.
