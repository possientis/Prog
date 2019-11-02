lemma L1 : ∀ (p q:Prop), p → p ∨ q :=
  λ p q hp, or.intro_left q hp

#check L1

lemma L2 : ∀ (p q:Prop), q → p ∨ q :=
  λ p q hq, or.intro_right p hq

#check L2

#check or.elim -- Either a b -> (a -> c) -> (b _> c) -> c

lemma L3 : ∀ (p q:Prop), p ∨ q → q ∨ p :=
  λ p q h, or.elim h (or.intro_right q) (or.intro_left p)

#check L3
