universe u

def LEM   : Prop := ∀ (A:Prop), A ∨ ¬A
def IRREL : Prop := ∀ (A:Prop) (p q:A), p = q

-- Proof irrelevance is true in lean by default, unlike Coq
lemma L1 : IRREL :=
  assume A p q,
    begin
      simp
    end

lemma L2 : IRREL := λ (A:Prop) (p:A) (q:A), rfl

inductive Accessible {α : Sort u} (r : α → α → Prop) : α → Prop
| MkAcc : ∀ (x:α), (∀ (y:α), r y x → Accessible y) → Accessible x

def WellFounded (α : Sort u) (r : α → α → Prop) : Prop := ∀ (x:α), Accessible r x

lemma AccessibleInv' : ∀ (α : Sort u) (r : α → α → Prop) (x : α),
  Accessible r x -> ∀ (y:α), r y x -> Accessible r y :=
    assume a r x H,
      begin
        cases H with x H,
        assumption
      end

