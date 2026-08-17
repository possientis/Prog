Declare Scope ZF_Notation_ProdGen_scope.
Open    Scope ZF_Notation_ProdGen_scope.

Class ProdGen (v w:Type) := { prodGen : v -> w -> v }.

Notation ":prd:_{ p } q" := (prodGen p q)
  (at level 1, no associativity) : ZF_Notation_ProdGen_scope.

