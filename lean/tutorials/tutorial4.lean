import data.real.basic
import data.int.parity

open nat

example : ∃ (n : ℕ), 8 = 2*n :=
begin
  use 4, refl
end

example : ∀ (n : ℕ), (exists (k : ℕ), n = k + 1) → n > 0 :=
begin
  intros n H₁, cases H₁ with k H₁, rw H₁, apply succ_pos
end

example : ∀ (a b c : ℤ), a ∣ b → b ∣ c → a ∣ c :=
begin
  intros a b c H₁ H₂,
  cases H₁ with n H₁, cases H₂ with m H₂, use (n*m), calc
  c   = b*m     : by assumption
  ... = (a*n)*m : by rw H₁
  ... = a*(n*m) : by ring
end

example : ∀ (a b c : ℤ), a ∣ b → a ∣ c → a ∣ b + c :=
begin
  intros a b c H₁ H₂,
  rcases H₁ with ⟨n, H₁⟩, rcases H₂ with ⟨m,H₂⟩, use (n + m),
  rw [H₁,H₂], ring
end
