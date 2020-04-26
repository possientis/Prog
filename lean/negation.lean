lemma L1 : ∀ (p q:Prop), (p → q) → ¬q → ¬p :=
  λ p q h nq hp, nq (h hp)

--#check L1

lemma L1' : ∀ (p q:Prop), (p → q) → ¬q → ¬p :=
  λ p q hpq hnq,
    assume hp : p,
    show false, from hnq (hpq hp)

--#check L1'


lemma L2 : ∀ (p q:Prop), p → ¬p → q :=
  λ p q hp hnp, false.elim (hnp hp)


--#check L2

lemma L2' : ∀ (p q:Prop), p → ¬p → q :=
  λ p q hp hnp, absurd hp hnp

--#check L2'

lemma L3 : ∀ (p q r:Prop), ¬p → q → (q → p) → r :=
  λ p q r hnp hq hqp, absurd (hqp hq) hnp

--#check L3
