lemma L1 : ∀ (p q:Prop), p → p ∨ q :=
  λ p q hp, or.intro_left q hp

--#check L1

lemma L2 : ∀ (p q:Prop), q → p ∨ q :=
  λ p q hq, or.intro_right p hq

--#check L2

--#check or.elim -- Either a b -> (a -> c) -> (b _> c) -> c

lemma L3 : ∀ (p q:Prop), p ∨ q → q ∨ p :=
  λ p q h, or.elim h (or.intro_right q) (or.intro_left p)

--#check L3


lemma L3' : ∀ (p q:Prop), p ∨ q → q ∨ p :=
  λ p q h, or.elim h
    (assume hp : p, show q ∨ p, from or.intro_right q hp)
    (assume hq : q, show q ∨ p, from or.intro_left  p hq)

--#check L3'

lemma L4 : ∀ (p q:Prop), p ∨ q → q ∨ p :=
  λ p q h, or.elim h (λ hp, or.inr hp) (λ hq, or.inl hq)

--#check L4


lemma L4' : ∀ (p q:Prop), p ∨ q → q ∨ p :=
  λ p q h, h.elim (λ hp, or.inr hp) (λ hq, or.inl hq)

--#check L4'
