Declare Scope ZF_Notation_Eval2_scope.
Open    Scope ZF_Notation_Eval2_scope.

Require Import ZF.Set.Core.

Class Eval2 (u v w:Type) := { eval2 : u -> v -> w }.

Notation "F $ a" := (eval2 F a)
  (at level 0, no associativity) : ZF_Notation_Eval2_scope.

