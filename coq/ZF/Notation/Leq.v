Declare Scope ZF_Core_Leq_scope.
Open    Scope ZF_Core_Leq_scope.

Class Leq (v:Type) := { leq : v -> v -> Prop }.

Notation "x :<=: y" := (leq x y)
  (at level 50, no associativity) : ZF_Core_Leq_scope.
