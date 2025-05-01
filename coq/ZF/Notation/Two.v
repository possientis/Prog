Declare Scope ZF_Notation_Two_scope.
Open    Scope ZF_Notation_Two_scope.

Class Two (v:Type) := { two : v }.

Notation ":2:" := two
  (at level 0, no associativity) : ZF_Notation_Two_scope.


