Declare Scope ZF_Notation_SupBelow_scope.
Open    Scope ZF_Notation_SupBelow_scope.

Require Import ZF.Set.Core.

Class SupBelow (v:Type) := { supBelow : U -> v -> v }.

Notation "sup(:< b ) A" := (supBelow b A)
  (at level 0, no associativity): ZF_Notation_SupBelow_scope.
