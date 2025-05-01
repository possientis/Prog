Declare Scope ZF_Notation_Three_scope.
Open    Scope ZF_Notation_Three_scope.

Class Three (v:Type) := { three : v }.

Notation ":3:" := three
  (at level 0, no associativity) : ZF_Notation_Three_scope.


