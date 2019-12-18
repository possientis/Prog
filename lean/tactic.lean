lemma L1 : ∀ (p q:Prop), p → q → p ∧ q ∧ p :=
  assume p q hp hq,
    begin
      apply and.intro,
      exact hp,
      apply and.intro,
      exact hq,
      exact hp
    end

#check L1
#print L1

lemma L2 : ∀ (p q:Prop), p → q → p ∧ q ∧ p :=
  assume p q hp hq,
    begin
      apply and.intro hp,
      exact and.intro hq hp
    end

#print L2


lemma L3 : ∀ (p q:Prop), p → q → p ∧ q ∧ p :=
  assume p q hp hq,
    begin
      apply and.intro hp;     -- semi-colon is fine too
      exact and.intro hq hp
    end

lemma L4 : ∀ (p q:Prop), p → q → p ∧ q ∧ p :=
  assume p q hp hq,
    by exact and.intro hp (and.intro hq hp)


variables {p q : Prop} (hp : p) (hq : q)

include hp hq    -- bring those into context needed for proof

example : p ∧ q ∧ p :=
  begin
    apply and.intro hp,
    exact and.intro hq hp
  end

omit hp hq      -- cancels previous 'include' directive

lemma L5 : ∀ (p q r : Prop), p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  assume p q r,
    begin
      apply iff.intro,
      intro H -- TODO
    end






