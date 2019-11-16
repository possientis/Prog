lemma L1 : ∀ (α : Type) (p q : α → Prop),
  (∀ (x:α), p x ∧ q x) → ∀ (y:α), p y :=
  λ α p q H y, show p y, from (H y).left


#check L1

lemma L2 : ∀ (α : Type) (p q : α → Prop),
  (∀ (x:α), p x ∧ q x) → ∀ (y:α), p y :=
  assume α p q H y, show p y, from
    (H y).left

#check L2
