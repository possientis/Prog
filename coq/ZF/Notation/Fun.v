Declare Scope ZF_Notation_Fun_scope.
Open    Scope ZF_Notation_Fun_scope.

Class Fun (v w:Type) := { IsFun : v -> w -> w -> Prop }.

Notation "F :: A :-> B" := (IsFun F A B)
  (at level 0, no associativity) : ZF_Notation_Fun_scope.
