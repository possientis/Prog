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


example : ∀ (a b c : ℝ), 0 ≤ c → a ≤ b → a*c ≤ b*c :=
begin
  intros a b c H₁ H₂,
  have H₃ : 0 ≤ b - a               ,{ rw sub_nonneg, assumption },
  have H₄ : 0 ≤ (b - a)*c           ,{ apply mul_nonneg; assumption },
  have H₅ : (b - a)*c = b*c - a*c   ,{ ring },
  have H₆ : 0 ≤ b*c - a*c           ,{ rw ← H₅, assumption },
  rw ← sub_nonneg, assumption
end

-- Slightly shorter using 'rwa' tactic
example : ∀ (a b c : ℝ), 0 ≤ c → a ≤ b → a*c ≤ b*c :=
begin
  intros a b c H₁ H₂,
  have H₃ : 0 ≤ b - a               ,{ rwa sub_nonneg },
  have H₄ : 0 ≤ (b -a)*c            ,{ apply mul_nonneg; assumption },
  have H₅ : (b - a)*c = b*c - a*c   ,{ ring },
  have H₆ : 0 ≤ b*c - a*c           ,{ rwa ← H₅ },
  rwa ← sub_nonneg
end

example : ∀ (a b c : ℝ), 0 ≤ c → a ≤ b → a*c ≤ b*c :=
begin
  intros a b c H₁ H₂, rw ← sub_nonneg, calc
  0   ≤ (b - a)*c     : mul_nonneg (by rwa sub_nonneg) H₁
  ... = b*c - a*c     : by ring,
end

-- Backward reasoning
example : ∀ (a b c : ℝ), c ≤ 0 → a ≤ b → b*c ≤ a*c :=
begin
  intros a b c H₁ H₂, rw ← sub_nonneg,
  have H₃ : a*c - b*c = (a - b)*c, { ring },
  rw H₃,
  apply mul_nonneg_of_nonpos_of_nonpos; try { assumption },
  rwa sub_nonpos
end

-- Forward reasoning
example : ∀ (a b c : ℝ), c ≤ 0 → a ≤ b → b*c ≤ a*c :=
begin
  intros a b c H₁ H₂,
  have H₃ : a - b ≤ 0, { rwa sub_nonpos },
  have H₄ : 0 ≤ (a - b)*c, { apply mul_nonneg_of_nonpos_of_nonpos; assumption },
  have H₅ : (a - b)*c = a*c - b*c, { ring },
  have H₆ : 0 ≤ a*c - b*c, { rwa ← H₅ },
  rwa ← sub_nonneg
end

example : ∀ (a b c : ℝ), c ≤ 0 → a ≤ b → b*c ≤ a*c :=
begin
  intros a b c H₁ H₂, rw ← sub_nonneg, calc
  0   ≤ (a - b)*c      : mul_nonneg_of_nonpos_of_nonpos (by rwa sub_nonpos) H₁
  ... = a * c - b* c   : by ring
end

example : ∀ (P Q R : Prop), (P ∧ Q → R) ↔ (P → Q → R) :=
begin
  intros P Q R, split; intros H₁,
    { intros H₂ H₃, apply H₁, split; assumption },
    { rintros ⟨H₂,H₃⟩, apply H₁; assumption }
end

example : ∀ (a b : ℝ), 0 ≤ b → a ≤ a + b :=
begin
  intros a b H₁, linarith
end

example : ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → 0 ≤ a + b :=
begin
  intros a b H₁ H₂, linarith
end


example : ∀ (a b c d : ℝ), a ≤ b → c ≤ d → a + c ≤ b + d :=
begin
  intros a b c d H₁ H₂, linarith
end

open nat

example : ∀ (a b : ℕ), a ∣ b ↔ gcd a b = a := -- '∣' is \| ... not just |
begin
  intros a b, split; intros H₁,
    { apply dvd_antisymm,
      { apply gcd_dvd_left },
      { rw dvd_gcd_iff, split,
        { apply dvd_refl},
        { assumption }}},
    { rw ← H₁, apply gcd_dvd_right }
end


