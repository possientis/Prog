Declare Scope ZF_Notation_Not_scope.
Open    Scope ZF_Notation_Not_scope.

Class Not (v:Type) := { not : v -> v }.

Notation ":¬: a" := (not a)
  (at level 0, a at level 10) : ZF_Notation_Not_scope.

