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
lemma seqReduce : ∀ (e₁ e₂:Stmt) (s:Env),
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

lemma ValueIsSkip : ∀ (e:Stmt) (s:Env), Value e s ↔ e = skip :=
begin
  intros e s, split; intros H,
    { unfold Value at H, revert s,
      cases e with x a e₁ e₂ b e₁ e₂ b e₁; intros s H,
        { refl },
        { exfalso, apply H, existsi skip, existsi (bindVar x a s), constructor },
        { exfalso, apply H, apply seqReduce },
        { exfalso, apply H, cases (LEM (b s)),
          { existsi e₁, existsi s, constructor, assumption },
          { existsi e₂, existsi s, constructor, assumption }},
        { exfalso, apply H, existsi (ite b (e₁ ;; while b e₁) skip),
          existsi s, constructor}},
    { intros H1, cases H1 with e' H1, cases H1 with s' H1,
      cases H1 with x a H1 e₁ e₁' e₂ H1 _ _ _ _ b _ e H1 _ b e₁ H1 _ _ b e₁ H1,
        { cases H },
        { cases H },
        { cases H },
        { cases H },
        { cases H },
        { cases H }}
end

lemma ReduceDeterministic : ∀ (e e₁ e₂:Stmt) (s s₁ s₂:Env),
  Reduce e s e₁ s₁ → Reduce e s e₂ s₂ → e₁ = e₂ ∧ s₁ = s₂ :=
begin
  intros e e₁ e₂ s s₁ s₂ H1, revert e₂ s₂,
  induction H1 with x a s e' e₁ e₂ s' s₁ H1 IH;
  intros e₂ s₂ H2,
    { cases H2, split, { refl }, { unfold bindVar}},
    { cases H2 with _ _ _ _ e₁',
      {},
      {}},
    {},
    {},
    {},
    {}
end


