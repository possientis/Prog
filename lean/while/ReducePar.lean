import Stmt
import Reduce

open list
open Stmt

inductive ReducePar : list Stmt → Env → list Stmt → Env → Prop
| Step : ∀ (e₁ e₂:Stmt) (s₁ s₂:Env) (es : list Stmt),
    Reduce e₁ s₁ e₂ s₂ → ReducePar (e₁ :: es) s₁ (e₂ :: es) s₂
| Cons : ∀ (es₁ es₂:list Stmt) (s₁ s₂:Env) (e:Stmt),
    ReducePar es₁ s₁ es₂ s₂ → ReducePar (e :: es₁) s₁ (e :: es₂) s₂

def p₀ : Stmt := "x" :== aNum 42
def p₁ : Stmt := "x" :== aNum 99

