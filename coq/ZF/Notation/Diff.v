Declare Scope ZF_Notation_Diff_scope.
Open    Scope ZF_Notation_Diff_scope.

Class Diff (v:Type) := { diff : v -> v -> v }.

Notation "a :\: b" := (diff a b)
  (at level 66, left associativity) : ZF_Notation_Diff_scope.


