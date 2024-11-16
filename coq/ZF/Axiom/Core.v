Declare Scope ZF_Core_scope.
Open    Scope ZF_Core_scope.

(* There is a universe of sets                                                  *)
Axiom U : Type.

(* There is a fundamental membership predicate between sets                     *)
Axiom Elem : U -> U -> Prop.

Notation "x :< y" := (Elem x y)
  (at level 6, no associativity) : ZF_Core_scope.

