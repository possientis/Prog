open classical

variable p : Prop

#check em p -- law of excluded middle

-- This requres law of exlcuded middle
lemma L1 : ∀ (p:Prop), ¬¬p → p := λ p h,
  or.elim (em p)
    (assume hp : p, hp)
    (assume hnp : ¬p, absurd hnp h)


#check L1


lemma L2 : ∀ (p:Prop), ¬¬p → p := λ p h,
  by_cases
    (assume h1:p, h1)
    (assume h1:¬p, absurd h1 h)

#check L2


lemma L3 : ∀ (p:Prop), ¬¬p → p := λ p h,
  by_contradiction
    (assume h1:¬p,
      show false, from h h1)

#check L3


lemma L4 : ∀ (p q:Prop), ¬(p ∧ q) → ¬p ∨ ¬q := λ p q h,
  or.elim (em p) -- p ∨ ¬p
    (assume hp:p, or.inr
      (show ¬q, from
        (assume hq:q, h ⟨hp,hq⟩)))
    (assume hp:¬p, or.inl
      (show ¬p, from
        hp))

#check L4


lemma L5 : ∀ (p q:Prop), ¬(p ∧ q) → ¬p ∨ ¬q := λ p q h,
  or.elim (em p)
    (assume hp: p, or.inr
      (show ¬q, from
        (assume hq:q, h ⟨hp,hq⟩)))
    (assume hp:¬p, or.inl hp)

#check L5


