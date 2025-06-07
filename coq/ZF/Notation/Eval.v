Declare Scope ZF_Notation_Eval_scope.
Open    Scope ZF_Notation_Eval_scope.

Require Import ZF.Set.Core.

Class Eval (v:Type) := { eval : v -> U -> U }.

Notation "F ! a" := (eval F a)
  (at level 0, no associativity) : ZF_Notation_Eval_scope.

