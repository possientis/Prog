import tuto_lib
import data.int.parity


example : false → 0 = 1 :=
begin
  intros H₁, exfalso, assumption
end

example : ∀ (x : ℝ), ¬ x < x :=
begin
  intros x H₁, rw lt_iff_le_and_ne at H₁, cases H₁ with H₁ H₂, clear H₁,
  change x = x → false at H₂, apply H₂, refl
end

open int

example : ∀ (n : ℤ), even n → ¬ even n → 0 = 1 :=
begin
  intros n H₁ H₂, exfalso, apply H₂, assumption
end

example : ∀ (P Q:Prop), (P ∨ Q) → ¬(P ∧ Q) → ¬ P ↔ Q :=
begin
  intros P Q, intros H₁,
end
