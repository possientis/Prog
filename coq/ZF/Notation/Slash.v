Declare Scope ZF_Notation_Slash_scope.
Open    Scope ZF_Notation_Slash_scope.

Class Slash (v w:Type) := { slash : v -> w -> w }.

Notation "a :/: b" := (slash a b)
  (at level 13, left associativity) : ZF_Notation_Slash_scope.


