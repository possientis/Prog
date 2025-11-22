Declare Scope ZF_Notation_Mult_scope.
Open    Scope ZF_Notation_Mult_scope.

Class Mult (v:Type) := { mult : v -> v -> v }.

Notation "a :*: b" := (mult a b)
  (at level 40, left associativity) : ZF_Notation_Mult_scope.
