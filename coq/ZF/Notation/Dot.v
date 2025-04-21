Declare Scope ZF_Core_Dot_scope.
Open    Scope ZF_Core_Dot_scope.

Class Dot (v:Type) := { dot : v -> v -> v }.

Notation "a :.: b" := (dot a b)
  (at level 11, right associativity) : ZF_Core_Dot_scope.

