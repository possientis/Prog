Declare Scope ZF_Notation_Lt_scope.
Open    Scope ZF_Notation_Lt_scope.

Class Lt (v:Type) := { lt : v -> v -> Prop }.

Notation "x :<: y" := (lt x y)
  (at level 50, no associativity) : ZF_Notation_Lt_scope.
