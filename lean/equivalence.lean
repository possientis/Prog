lemma L1 : ∀ (p q:Prop), p ∧ q ↔ q ∧ p :=
  λ p q, iff.intro
    (λ hpq, ⟨hpq.right,hpq.left⟩)
    (λ hqp, ⟨hqp.right, hqp.left⟩)

#check L1

lemma L1' : ∀ (p q:Prop), p ∧ q ↔ q ∧ p :=
  λ p q, iff.intro
    (assume h:p ∧ q, show q ∧ p, from ⟨h.right, h.left⟩)
    (assume h:q ∧ p, show p ∧ q, from ⟨h.right, h.left⟩)

#check L1'
