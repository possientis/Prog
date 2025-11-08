Declare Scope ZF_Notation_Plus_scope.
Open    Scope ZF_Notation_Plus_scope.

Class Plus (v:Type) := { plus : v -> v -> v }.

Notation "a :+: b" := (plus a b)
  (at level 15, left associativity) : ZF_Notation_Plus_scope.
