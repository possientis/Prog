Declare Scope ZF_Notation_Diff_scope.
Open    Scope ZF_Notation_Diff_scope.

Class Diff (v w:Type) := { diff : v -> w -> v }.

Notation "a :\: b" := (diff a b)
  (at level 59, left associativity) : ZF_Notation_Diff_scope.


