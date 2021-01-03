import data.real.basic
import algebra.group.pi

notation `|`x`|` := abs x

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

variables (u v w : ℕ → ℝ) (l l' : ℝ)

example : (∀ n, u n = l) → seq_limit u l :=
begin
  intros H₁ ε H₂, use 0, intros n H₃, rw H₁, norm_num, linarith
end


example : l > 0 → seq_limit u l → ∃ N, ∀ n ≥ N, u n ≥ l/2 :=
begin
  intros H₁ H₂, specialize H₂ (l/2) (by linarith),
  cases H₂ with N H₂, use N, intros n H₃, specialize H₂ n H₃,
  rw abs_le at H₂, cases H₂ with H₂ H₄, linarith
end

example : seq_limit u l → seq_limit v l' → seq_limit (u + v) (l + l') :=
begin
  intros H₁ H₂ ε H₃,
  specialize H₁ (ε/2) (by linarith), cases H₁ with N₁ H₁,
  specialize H₂ (ε/2) (by linarith), cases H₂ with N₂ H₂,
  use max N₁ N₂, intros n H₃,
  rw ge_max_iff at H₃,
end
