Declare Scope ZF_Notation_Exp2_scope.
Open    Scope ZF_Notation_Exp2_scope.


Class Exp2 (v:Type) := { exp2 : v -> v -> v }.


Notation "a :^^: b" := (exp2 a b)
  (at level 30, right associativity) : ZF_Notation_Exp2_scope.

