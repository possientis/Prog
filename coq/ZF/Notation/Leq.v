Declare Scope ZF_Notation_Leq_scope.
Open    Scope ZF_Notation_Leq_scope.

Class Leq (v:Type) := { leq : v -> v -> Prop }.

Notation "x :<=: y" := (leq x y)
  (at level 50, no associativity) : ZF_Notation_Leq_scope.
