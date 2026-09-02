Declare Scope ZF_Notation_Equiv_scope.
Open    Scope ZF_Notation_Equiv_scope.

Class Equiv (v:Type) := { equiv : v -> v -> Prop }.

Notation "x :~: y" := (equiv x y)
  (at level 70, no associativity) : ZF_Notation_Equiv_scope.

Notation "x :<>: y" := (~ equiv x y)
  (at level 70, no associativity) : ZF_Notation_Equiv_scope.
