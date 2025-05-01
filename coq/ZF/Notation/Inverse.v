Declare Scope ZF_Notation_Inverse_scope.
Open    Scope ZF_Notation_Inverse_scope.

Class Inverse (v:Type) := { inverse : v -> v }.

Notation "F ^:-1:" := (inverse F)
  (at level 0, no associativity) : ZF_Notation_Inverse_scope.

