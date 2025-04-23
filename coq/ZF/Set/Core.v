Declare Scope ZF_Set_scope.
Open    Scope ZF_Set_scope.

(* There is a universe of sets                                                  *)
Axiom U : Type.

(* There is a fundamental membership predicate between sets                     *)
Axiom Elem : U -> U -> Prop.

Notation "x :< y" := (Elem x y)
  (at level 20, no associativity) : ZF_Set_scope.
