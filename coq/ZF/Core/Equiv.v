Declare Scope ZF_Core_Equiv_scope.
Open    Scope ZF_Core_Equiv_scope.

Class Equiv (v:Type)
  := { equiv : v -> v -> Prop
     ; EquivRefl : forall (x:v), equiv x x
     ; EquivSym  : forall (x y:v), equiv x y -> equiv y x
     ; EquivTran : forall (x y z:v), equiv x y -> equiv y z -> equiv x z
     }.

Notation "x == y" := (equiv x y)
  (at level 50, no associativity) : ZF_Core_Equiv_scope.

(* Predicate expressing the fact a function is compatible with equivalences.    *)
Definition EquivCompat (v w:Type) (p:Equiv v) (q:Equiv w) (f:v -> w) : Prop :=
  forall (x y:v), x == y -> f x == f y.

Arguments EquivCompat {v} {w} {p} {q}.
