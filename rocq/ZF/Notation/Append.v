Declare Scope ZF_Notation_Append_scope.
Open    Scope ZF_Notation_Append_scope.

Class Append (v:Type) := { append : v -> v -> v }.

Notation "a :++: b" := (append a b)
  (at level 60, right associativity) : ZF_Notation_Append_scope.
