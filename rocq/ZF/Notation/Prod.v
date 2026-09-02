Declare Scope ZF_Notation_Prod_scope.
Open    Scope ZF_Notation_Prod_scope.

Class Prod (v:Type) := { prod : v -> v -> v }.

Notation "a :x: b" := (prod a b)
  (at level 40, left associativity) : ZF_Notation_Prod_scope.


