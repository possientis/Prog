Declare Scope ZF_Notation_And_scope.
Open    Scope ZF_Notation_And_scope.

Class And (v:Type) := { and : v -> v -> v }.

Notation "a :/\: b" := (and a b)
  (at level 60, right associativity) : ZF_Notation_And_scope.
