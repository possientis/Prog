Declare Scope Prop_Syntax_scope.

(* Given a type v of all propositional variables, defines the the P v of all    *)
(* formulas of propositional logic with atoms in v                              *)
Inductive P (v:Type) : Type :=
| Bot : P v
| Var : v -> P v
| Imp : P v -> P v -> P v
.
