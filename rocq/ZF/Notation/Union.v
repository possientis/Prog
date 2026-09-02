Declare Scope ZF_Notation_Union_scope.
Open    Scope ZF_Notation_Union_scope.

Class Union (v:Type) := { union : v -> v }.

Notation ":U( a  )" := (union a)
  (at level 0, no associativity) : ZF_Notation_Union_scope.

