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

example : ∀ (a : ℤ), 0 ∣ a ↔ a = 0 :=
begin
  intros a, split; intros H₁,
    { cases H₁ with k H₁, rw H₁, ring },
    { use 0, rw H₁, ring }
end

open function

example : ∀ (f g : ℝ → ℝ), surjective (g ∘ f) → surjective g :=
begin
  intros f g H₁ y, cases (H₁ y) with x H₁, use (f x), assumption
end

example : ∀ (f g : ℝ → ℝ), surjective f → surjective g → surjective (g ∘ f) :=
begin
  intros f g H₁ H₂ y,
  cases (H₂ y) with y' H₂,
  cases (H₁ y') with x H₁,
  use x, simp, rw H₁, assumption
end
