import data.real.basic
import tactic.suggest

noncomputable theory
open_locale classical

--#check upper_bounds

def up_bounds (A : set ℝ) := { a : ℝ | ∀ x ∈ A, x ≤ a }

def is_max (a : ℝ) (A : set ℝ) := a ∈ A ∧ a ∈ up_bounds A

infix ` is_a_max_of `:55 := is_max

lemma unique_max : ∀ (A : set ℝ) (x y : ℝ),
  x is_a_max_of A →
  y is_a_max_of A →
  x = y
:= begin
  intros A x y H₁ H₂,
  cases H₁ with H₁ H₃, unfold up_bounds at H₃, simp at H₃,
  cases H₂ with H₂ H₄, unfold up_bounds at H₄, simp at H₄,
  specialize H₃ y H₂,
  specialize H₄ x H₁,
  linarith
end

example : ∀ (A : set ℝ) (x y : ℝ),
  x is_a_max_of A →
  y is_a_max_of A →
  x = y
:= begin
  intros A x y Hx Hy,
  have : x ≤ y, from Hy.2 _ Hx.1,
  have : y ≤ x, from Hx.2 _ Hy.1,
  linarith
end


