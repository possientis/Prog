Declare Scope ZF_Notation_N_scope.
Open    Scope ZF_Notation_N_scope.


Class N (v:Type) := { omega : v }.

Notation ":N" := omega
  (at level 0, no associativity) : ZF_Notation_N_scope.
