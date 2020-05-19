axiom propext2 {p q : Prop} : (p ↔ q) → p = q

--#check @propext2
--#check @propext

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
lemma L3 :
  (∀ (p q : Prop), (p ↔ q) → p = q)
  ↔
  (∀ (P : Prop → Prop) (p q:Prop), (p ↔ q) → (P p → P q)) :=
begin
  split,
    {intros H1 P p q H2 H3, rewrite ← (H1 p q H2), assumption},
    {intros H1 p q H2, apply H1 (λ z, p = z) p q H2 rfl}
end
