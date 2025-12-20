Declare Scope ZF_Notation_Exp_scope.
Open    Scope ZF_Notation_Exp_scope.


Class Exp (v:Type) := { exp : v -> v -> v }.


Notation "a :^: b" := (exp a b)
  (at level 30, right associativity) : ZF_Notation_Exp_scope.

