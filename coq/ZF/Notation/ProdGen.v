Declare Scope ZF_Notation_ProdGen_scope.
Open    Scope ZF_Notation_ProdGen_scope.

Class ProdGen (u v w:Type) := { prodGen : u -> v -> w }.

Notation ":prd:_{ p } q" := (prodGen p q)
  (at level 1, no associativity) : ZF_Notation_ProdGen_scope.

