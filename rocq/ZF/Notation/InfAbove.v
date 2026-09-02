Declare Scope ZF_Notation_InfAbove_scope.
Open    Scope ZF_Notation_InfAbove_scope.

Require Import ZF.Set.Core.

Class InfAbove (v:Type) := { infAbove : U -> v -> v }.

Notation "inf(>: b ) A" := (infAbove b A)
  (at level 0, no associativity): ZF_Notation_InfAbove_scope.
