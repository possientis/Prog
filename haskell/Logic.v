Inductive Expr (v:Type) : Type :=
| In    : v -> v -> Expr v
| Bot   : Expr v
| Imply : Expr v -> Expr v -> Expr v
| Forall: v -> Expr v -> Expr v
.
