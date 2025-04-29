Declare Scope ZF_Core_Inter_scope.
Open    Scope ZF_Core_Inter_scope.

Class Inter (v:Type) := { inter : v -> v }.

Notation ":I( a  )" := (inter a)
  (at level 0, no associativity) : ZF_Core_Inter_scope.

