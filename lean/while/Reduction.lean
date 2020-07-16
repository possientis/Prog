import Stmt

open Stmt

axiom LEM : forall (p:Prop), p ∨ ¬p

-- Small step semantics, aka reduction relation
inductive Reduce : Stmt → Env → Stmt → Env → Prop
| ASN     : ∀ (x:string) (a:AExp) (s:Env), Reduce (assign x a) s skip (bindVar x a s)
| SEQ_STEP: ∀ (e₁ e₁' e₂:Stmt) (s s':Env),
    Reduce e₁ s e₁' s' →
    Reduce (e₁ ;; e₂) s (e₁' ;; e₂) s'
| SEQ_SKIP: ∀ (e:Stmt) (s:Env), Reduce (skip ;; e) s e s
| IF_T    : ∀ (b:BExp) (e₁ e₂:Stmt) (s:Env), b s → Reduce (ite b e₁ e₂) s e₁ s
| IF_F    : ∀ (b:BExp) (e₁ e₂:Stmt) (s:Env), ¬ b s → Reduce (ite b e₁ e₂) s e₂ s
| WHILE   : ∀ (b:BExp) (e:Stmt) (s:Env),
    Reduce (while b e) s (ite b (e ;; (while b e)) skip) s

open Reduce

-- Predicate expressing that no further reduction is possible
def Value (e:Stmt) (s:Env) : Prop := ¬ (∃ (e':Stmt) (s':Env), Reduce e s e' s')

-- Sequential statement always reduces
lemma seq_reduce : ∀ (e₁ e₂:Stmt) (s:Env),
  (∃ (e':Stmt) (s':Env), Reduce (e₁ ;; e₂) s e' s') :=
begin
  intros e₁, induction e₁ with x a e₁ e₁' IH1 IH1' b e₁ e₁' IH1 IH1' b e₁ IH1;
  intros e₂ s,
    { existsi e₂, existsi s, constructor },
    { existsi (skip ;; e₂), existsi (bindVar x a s), apply SEQ_STEP, apply ASN },
    { clear IH1', cases (IH1 e₁' s) with e H1, cases H1 with s' H1,
      existsi (e ;; e₂), existsi s', apply SEQ_STEP, assumption },
    { cases (LEM (b s)) with H1 H1,
      { existsi (e₁ ;; e₂), existsi s, apply SEQ_STEP, apply IF_T, assumption },
      { existsi (e₁' ;; e₂), existsi s, apply SEQ_STEP, apply IF_F, assumption }},
    { existsi ((ite b (e₁ ;; while b e₁) skip) ;; e₂), existsi s,
      apply SEQ_STEP, apply WHILE},
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
