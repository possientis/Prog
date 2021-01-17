import data.real.basic
import algebra.group.pi
import tuto_lib

notation `|`x`|` := abs x

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
  rw ge_max_iff at H₃, cases H₃ with H₃ H₄,
  specialize H₁ n H₃, specialize H₂ n H₄,
  calc
  |(u + v) n - (l + l')| = |u n + v n - (l + l')|   : rfl
               ...       = |(u n - l) + (v n - l')| : by { congr' 1, ring }
               ...       ≤ |u n - l| + |v n - l'|   : by apply abs_add
               ...       ≤ ε                        : by linarith
end

example :
  seq_limit u l →
  seq_limit w l →
  (∀ n, u n ≤ v n) →
  (∀ n, v n ≤ w n) →
  seq_limit v l :=
begin
  intros H₁ H₂ H₃ H₄ ε H₅,
  specialize H₁ ε H₅, specialize H₂ ε H₅,
  cases H₁ with N₁ H₁, cases H₂ with N₂ H₂,
  use max N₁ N₂, intros n H₆, rw ge_max_iff at H₆, cases H₆ with H₆ H₇,
  specialize H₁ n H₆, specialize H₂ n H₇,
  rw abs_le at H₁, cases H₁ with H₁ G₁,
  rw abs_le at H₂, cases H₂ with H₂ G₂,
  specialize H₃ n, specialize H₄ n,
  rw abs_le, split; linarith
end

example : seq_limit u l ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε :=
begin
  split; intros H₁,
    { intros ε H₂, specialize H₁ (ε/2) (by linarith), cases H₁ with N H₁,
      use N, intros n H₃, specialize H₁ n H₃, rw abs_le at H₁,
      cases H₁ with H₁ G₁, rw abs_lt, split; linarith },
    { intros ε H₂, specialize H₁ ε H₂, cases H₁ with N H₁,
      use N, intros n H₃, specialize H₁ n H₃, linarith }
end

example : seq_limit u l → seq_limit u l' → l = l' :=
begin
  intros H₁ H₂, apply eq_of_abs_sub_le_all, intros ε H₃,
  specialize H₁ (ε/2) (by linarith),
  specialize H₂ (ε/2) (by linarith),
  cases H₁ with N₁ H₁, cases H₂ with N₂ H₂,
  let N := max N₁ N₂,
  specialize H₁ N (le_max_left N₁ N₂),
  specialize H₂ N (le_max_right N₁ N₂),
  rw abs_le at H₁, cases H₁ with H₁ G₁,
  rw abs_le at H₂, cases H₂ with H₂ G₂,
  rw abs_le, split; linarith
end
