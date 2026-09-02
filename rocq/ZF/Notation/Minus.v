Declare Scope ZF_Notation_Minus_scope.
Open    Scope ZF_Notation_Minus_scope.

Class Minus (v:Type) := { minus : v -> v -> v }.

Notation "a :-: b" := (minus a b)
  (at level 50, left associativity) : ZF_Notation_Minus_scope.
