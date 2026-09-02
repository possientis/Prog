Declare Scope ZF_Notation_Zero_scope.
Open    Scope ZF_Notation_Zero_scope.

Class Zero (v:Type) := { zero : v }.

Notation ":0:" := zero
  (at level 0, no associativity) : ZF_Notation_Zero_scope.


