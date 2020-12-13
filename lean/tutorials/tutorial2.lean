import data.real.basic

example : ∀ (a b c : ℝ), a ≤ b → c + a ≤ c + b :=
begin
  intros a b c H₁, rw ← sub_nonneg,
  have H₂ : c + b - (c + a) = b - a, by ring,
  rw [H₂, sub_nonneg], assumption
end

example : ∀ (a b : ℝ), a ≤ b → ∀ (c : ℝ), a + c ≤ b + c :=
begin
  intros a b H₁ c, rw ← sub_nonneg,
  have H₂ : b + c - (a + c) = b - a, by ring,
  rw [H₂, sub_nonneg], assumption
end

example : ∀ (a b : ℝ), 0 ≤ a → b ≤ a + b :=
begin
  intros a b H₁,
  calc
    b   = 0 + b   : by rw zero_add
    ... ≤ a + b   : add_le_add_right H₁ b
end

example : ∀ (a b : ℝ), 0 ≤ b → a ≤ a + b :=
begin
  intros a b H₁,
  calc
    a   = a + 0   : by rw add_zero
    ... ≤ a + b   : add_le_add_left H₁ a
end

example : ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ a + b :=
begin
  intros a b H₁ H₂,
  calc
    0   = 0 + 0   : by rw add_zero
    ... ≤ a + 0   : add_le_add_right H₁ 0
    ... ≤ a + b   : add_le_add_left H₂ a
end

example : ∀ (a b c d : ℝ), a ≤ b → c ≤ d → a + c ≤ b + d :=
begin
  intros a b c d H₁ H₂,
  calc
    a + c ≤ b + c   : add_le_add_right H₁ c
    ...   ≤ b + d   : add_le_add_left H₂ b
end

example : ∀ (a b c : ℝ), 0 ≤ c → a ≤ b → a*c ≤ b*c  :=
begin
  intros a b c H₁ H₂, rw ← sub_nonneg,
  have H₃ : b*c - a*c = (b - a)*c, by ring,
  rw H₃, apply mul_nonneg; try {assumption},
  rw sub_nonneg, assumption
end






