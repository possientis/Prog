Declare Scope ZF_Notation_Sum_scope.
Open    Scope ZF_Notation_Sum_scope.

Class Sum (u v w:Type) := { sum : u -> v -> w }.

Notation ":sum:_{ a } f" := (sum a f)
  (at level 1, no associativity) : ZF_Notation_Sum_scope.

