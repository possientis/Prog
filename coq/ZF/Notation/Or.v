Declare Scope ZF_Notation_Or_scope.
Open    Scope ZF_Notation_Or_scope.

Class Or (v:Type) := { or : v -> v -> v }.

Notation "a :\/: b" := (or a b)
  (at level 15, right associativity) : ZF_Notation_Or_scope.
