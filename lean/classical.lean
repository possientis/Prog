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


lemma L6 : ∀ (p q:Prop), ¬(p ∧ q) → ¬p ∨ ¬q := λ p q h,
 or.elim (em p)
   (assume hp:p,
     or.inr (assume hq:q, (h ⟨hp,hq⟩)))
   (assume hp:¬p,
     or.inl hp)

lemma L7 : ∀ (p q r:Prop), p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := λ p q r,
  iff.intro
  (assume h : p ∧ (q ∨ r),
    (show p ∧ q ∨ p ∧ r, from
      (have hp:p, from and.left h,
        (have hqr:q∨r, from and.right h,
          (or.elim hqr
            (assume hq:q, or.inl ⟨hp,hq⟩)
            (assume hr:r, or.inr ⟨hp,hr⟩))))))
  (assume h: p ∧ q ∨ p ∧ r, or.elim h
    (assume hpq:p ∧ q,
      (have hp:p, from and.left hpq,
        (have hq:q, from and.right hpq,
          ⟨hp,or.inl hq⟩)))
    (assume hpr:p ∧ r,
      (have hp:p, from and.left hpr,
        (have hr:r, from and.right hpr,
          ⟨hp,or.inr hr⟩))))

#check L7


