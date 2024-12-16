Declare Scope ZF_Core_Equal_scope.
Open    Scope ZF_Core_Equal_scope.

Class Equal (v:Type) := { equal : v -> v -> Prop }.

Notation "x :~: y" := (equal x y)
  (at level 50, no associativity) : ZF_Core_Equal_scope.

(* Predicate expressing the fact a function is compatible with equivalences.    *)
Definition EqualCompat
  (v w:Type) (p:Equal v) (q:Equal w) (f:v -> w) : Prop :=
  forall (x y:v), x :~: y -> f x :~: f y.

Arguments EqualCompat {v} {w} {p} {q}.
