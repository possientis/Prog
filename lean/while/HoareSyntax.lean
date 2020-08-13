import Stmt
import Subst

open Stmt

inductive Hoare : Pred → Stmt → Pred → Prop
| SKIP   : ∀ (p:Pred), Hoare p skip p
| ASN    : ∀ (p:Pred) (x:string) (a:AExp), Hoare (subst x a p) (x :== a) p
| SEQ    : ∀ (p q r:Pred) (e₁ e₂:Stmt),
    Hoare p e₁ q → Hoare q e₂ r → Hoare p (e₁ ;; e₂) r
| IF     : ∀ (p q:Pred) (b:BExp) (e₁ e₂:Stmt),
    Hoare (λ s, p s ∧ b s)  e₁ q →
    Hoare (λ s, p s ∧ ¬b s) e₂ q →
    Hoare p (ite b e₁ e₂) q
| WHILE  : ∀ (p:Pred) (b:BExp) (e₁:Stmt),
    Hoare (λ s, p s ∧ b s) e₁ p → Hoare p (while b e₁) p
| WEAKEN : ∀ (p p' q q':Pred) (e₁:Stmt),
    (∀ s, p' s → p s) →
    Hoare p e₁ q      →
    (∀ s, q s → q' s) →
    Hoare p' e₁ q'




