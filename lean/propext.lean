axiom propext2 {p q : Prop} : (p ↔ q) → p = q

variables p q r s t : Prop
variable P : Prop -> Prop

lemma L1 : (p ↔ q) → ((r ∧ p ∧ s → t) ↔ (r ∧ q ∧ s → t)) :=
begin
  intros H,
  rewrite (propext2 H)
end

lemma L2 : (p ↔ q) → (P p → P q) :=
begin
  intros H1 H2,
  rewrite ← (propext2 H1),
  assumption
end

-- L2 is equivalent to propext
