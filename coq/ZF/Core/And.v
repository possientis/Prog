Declare Scope ZF_Core_And_scope.
Open    Scope ZF_Core_And_scope.

Class And (v:Type) := { and : v -> v -> v }.

Notation "a :/\: b" := (and a b)
  (at level 11, right associativity) : ZF_Core_And_scope.
