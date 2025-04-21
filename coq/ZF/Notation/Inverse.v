Declare Scope ZF_Core_Inverse_scope.
Open    Scope ZF_Core_Inverse_scope.

Class Inverse (v:Type) := { inverse : v -> v }.

Notation "F ^:-1:" := (inverse F)
  (at level 0, no associativity) : ZF_Core_Inverse_scope.

