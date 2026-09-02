Declare Scope ZF_Notation_InterGen_scope.
Open    Scope ZF_Notation_InterGen_scope.

Class InterGen (v w:Type) := { interGen : v -> w -> v }.

Notation ":/\:_{ p } q" := (interGen p q)
  (at level 1, no associativity) : ZF_Notation_InterGen_scope.

