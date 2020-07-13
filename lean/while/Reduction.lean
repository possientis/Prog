import Stmt

open Stmt

-- Small step semantics, aka reduction relation
inductive Reduce : Stmt → Env → Stmt → Env → Prop
| ASN     : ∀ (x:string) (a:AExp) (s:Env), Reduce (assign x a) s skip (bindVar x a s)
| SEQ_STEP: ∀ (e₁ e₁' e₂:Stmt) (s s':Env),
    Reduce e₁ s e₁' s' →
    Reduce (e₁ ;; e₂) s (skip ;; e₂) s'
| SEQ_SKIP: ∀ (e:Stmt) (s:Env), Reduce (skip ;; e) s e s
| IF_T    : TODO
