Declare Scope ZF_Core_Or_scope.
Open    Scope ZF_Core_Or_scope.

Class Or (v:Type) := { or : v -> v -> v }.

Notation "a :\/: b" := (or a b)
  (at level 12, right associativity) : ZF_Core_Or_scope.
