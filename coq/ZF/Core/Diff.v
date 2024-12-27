Declare Scope ZF_Core_Diff_scope.
Open    Scope ZF_Core_Diff_scope.

Class Diff (v:Type) := { diff : v -> v -> v }.

Notation "a :\: b" := (diff a b)
  (at level 13, left associativity) : ZF_Core_Diff_scope.


