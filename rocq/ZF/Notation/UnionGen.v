Declare Scope ZF_Notation_UnionGen_scope.
Open    Scope ZF_Notation_UnionGen_scope.

Class UnionGen (v w:Type) := { unionGen : v -> w -> v }.

Notation ":\/:_{ p } q" := (unionGen p q)
  (at level 1, no associativity) : ZF_Notation_UnionGen_scope.

