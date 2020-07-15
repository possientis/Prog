import Stmt

open Stmt

-- Small step semantics, aka reduction relation
inductive Reduce : Stmt → Env → Stmt → Env → Prop
| ASN     : ∀ (x:string) (a:AExp) (s:Env), Reduce (assign x a) s skip (bindVar x a s)
| SEQ_STEP: ∀ (e₁ e₁' e₂:Stmt) (s s':Env),
    Reduce e₁ s e₁' s' →
    Reduce (e₁ ;; e₂) s (skip ;; e₂) s'
| SEQ_SKIP: ∀ (e:Stmt) (s:Env), Reduce (skip ;; e) s e s
| IF_T    : ∀ (b:BExp) (e₁ e₂:Stmt) (s:Env), b s → Reduce (ite b e₁ e₂) s e₁ s
| IF_F    : ∀ (b:BExp) (e₁ e₂:Stmt) (s:Env), ¬ b s → Reduce (ite b e₁ e₂) s e₂ s
| WHILE   : ∀ (b:BExp) (e:Stmt) (s:Env),
    Reduce (while b e) s (ite b (e ;; (while b e)) skip) s

-- Predicate expressing that no further reduction is possible
def Value (e:Stmt) (s:Env) : Prop := ¬ (∃ (e':Stmt) (s':Env), Reduce e s e' s')

-- Sequential statement always reduces
lemma seq_reduce : ∀ (e₁ e₂:Stmt) (s:Env),
  (∃ (e':Stmt) (s':Env), Reduce (e₁ ;; e₂) s e' s') :=
begin
  intros e₁, cases e₁ with x a; intros e₂ s,
    {existsi e₂, existsi s, constructor},
    {},
    {},
    {},
    {},
    {},
end

lemma Value_is_skip : ∀ (e:Stmt) (s:Env), Value e s ↔ e = skip :=
begin
  intros e s, split; intros H,
    { unfold Value at H, revert s,
      cases e with x a e₁ e₂; intros s H,
        {refl},
        {exfalso, apply H, existsi skip, existsi (bindVar x a s), constructor},
        {exfalso, apply H, },
        {},
        {}
    },
    {}
end
