Declare Scope ZF_Notation_One_scope.
Open    Scope ZF_Notation_One_scope.

Class One (v:Type) := { one : v }.

Notation ":1:" := one
  (at level 0, no associativity) : ZF_Notation_One_scope.


