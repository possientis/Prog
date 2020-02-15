
inductive Expr : Type
| Const : ℕ → Expr
| Var   : ℕ → Expr
| Plus  : Expr → Expr → Expr
| Times : Expr → Expr → Expr

open Expr

def Env : Type := ℕ → ℕ

def eval (env : Env) (e: Expr) : ℕ :=
  Expr.rec_on e
    (λ n, n)
    (λ n, env n)
    (λ _ _ v1 v2, v1 + v2)
    (λ _ _ v1 v2, v1 * v2)

def env : Env := λ n, n


lemma L1 : eval env (Const 45) = 45 := rfl
lemma L2 : eval env (Var 34) = 34 := rfl
lemma L3 : eval env (Plus (Const 5) (Var 6)) = 11 := rfl
lemma L4 : eval env (Times (Const 5) (Const 6)) = 30 := rfl




