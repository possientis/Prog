universe u

class setoid2 (α : Sort u) : Sort (max 1 u) :=
  (r : α → α → Prop) (iseqv : equivalence r)

infix `≡` := setoid.r

--#check @setoid
--#check @setoid2
--#check (@setoid.iseqv α s).left

--#check @quot

def quotient2 {α : Sort u} (s : setoid α) := @quot α setoid.r

--#check @quotient
--#check @quotient2

--#check @quotient.mk
--#check @quotient.ind
--#check @quotient.lift   -- ≈ is \~~ or \approx
--#check @quotient.sound  -- ⟦ is \[[ , ⟧ is \]]
--#check @quotient.exact

def eqv {α : Type u} (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

infix `~` := eqv

lemma eqv_refl : ∀ {α : Type u} {p : α × α}, p ~ p :=
begin
  intros a p, left, split; reflexivity
end


lemma eqv_symm : ∀ {α : Type u} {p q : α × α}, p ~ q → q ~ p :=
begin
  intros α p q H, cases H with H H,
    {cases H with H1 H2, left, split; symmetry; assumption},
    {cases H with H1 H2, right, split; symmetry; assumption}
end

lemma eqv_trans : ∀ {α : Type u} {p q r : α × α}, p ~ q → q ~ r → p ~ r :=
begin
  intros α p q r H1 H2, cases H1 with H1 H1; cases H2 with H2 H2,
    { cases H1 with H1 H3, cases H2 with H2 H4, left, split;
      apply eq.trans; assumption},
    {},
    {},
    {},
end

