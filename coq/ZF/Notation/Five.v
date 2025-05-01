Declare Scope ZF_Notation_Five_scope.
Open    Scope ZF_Notation_Five_scope.

Class Five (v:Type) := { five : v }.

Notation ":5:" := five
  (at level 0, no associativity) : ZF_Notation_Five_scope.


