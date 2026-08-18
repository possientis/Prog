Declare Scope ZF_Notation_Successor_scope.
Open    Scope ZF_Notation_Successor_scope.

Class Successor (v:Type) := { successor : v -> v }.

Notation "a ^:+:" := (successor a)
  (at level 0, no associativity) : ZF_Notation_Successor_scope.
