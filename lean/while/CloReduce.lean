import Stmt
import Reduce

-- Reflexive, transtitive closure of small step semantics
inductive CloReduce : Stmt → Env → Stmt → Env → Prop
| cloRefl : ∀ (e:Stmt) (s:Env), CloReduce e s e s
| cloStep : ∀ (e₁ e₂ e₃:Stmt) (s₁ s₂ s₃:Env),
          Reduce e₁ s₁ e₂ s₂ → CloReduce e₂ s₂ e₃ s₃ → CloReduce e₁ s₁ e₃ s₃

open CloReduce

-- Reduce is a sub-relation of CloReduce
lemma ReduceCloReduce : ∀ (e₁ e₂:Stmt) (s₁ s₂:Env),
  Reduce e₁ s₁ e₂ s₂ → CloReduce e₁ s₁ e₂ s₂ :=
begin
  intros e₁ e₂ s₁ s₂ H1, apply cloStep,
    { assumption },
    { constructor }
end

-- CloReduce is indeed a transitive relation
lemma CloReduceTrans : ∀ (e₁ e₂ e₃:Stmt) (s₁ s₂ s₃:Env),
  CloReduce e₁ s₁ e₂ s₂ → CloReduce e₂ s₂ e₃ s₃ → CloReduce e₁ s₁ e₃ s₃ :=
begin
  intros e₁ e₂ e₃ s₁ s₂ s₃ H1, revert e₃ s₃,
  induction H1 with e₂ s₂ e₁ e₂ e₃ s₁ s₂ s₃ H1 H2 IH,
    { intros e₃ s₃ H1, assumption },
    { intros e₄ s₄ H3, apply cloStep,
      { apply H1 },
      { apply IH, assumption }}
end

-- Expresses that a relation is reflexive and transitive
def Closure {α:Type} (r:α → α → Prop) : Prop :=
  (∀ (x:α), r x x) ∧ (∀ (x y z:α), r x y → r y z → r x z)

-- CloReduce is indeed the smallest reflexive transitive relation
-- on Stmt × Env, which contains the relation Reduce
lemma CloReduceMinimal : ∀ (r:Stmt × Env → Stmt × Env → Prop),
  Closure r →
  (∀ (e₁ e₂:Stmt) (s₁ s₂:Env), Reduce e₁ s₁ e₂ s₂ → r (e₁,s₁) (e₂,s₂)) →
   ∀ (e₁ e₂:Stmt) (s₁ s₂:Env), CloReduce e₁ s₁ e₂ s₂ → r (e₁,s₁) (e₂,s₂) :=
begin
  intros r H1 H3, cases H1 with H1 H2,
  intros e₁ e₂ s₁ s₂ H4, induction H4 with e₁ s₁ e₁ e₂ e₃ s₁ s₂ s₃ H4 H5 IH,
    { apply H1 },
    { apply H2,
      { apply H3, apply H4},
      { assumption }}
end
