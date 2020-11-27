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

def low_bounds (A : set ℝ) := { a : ℝ | ∀ x ∈ A, a ≤ x }

def is_inf (a : ℝ) (A : set ℝ) := a is_a_max_of (low_bounds A)

infix ` is_an_inf_of `:55 := is_inf

lemma inf_lt {A : set ℝ} {a : ℝ} : a is_an_inf_of A →
  ∀ x, a < x → ∃ y ∈ A, y < x
:= begin
  intros H₁ x,
  contrapose,
  push_neg,
  intros H₂,
  unfold is_inf at H₁, unfold is_max at H₁, cases H₁ with H₁ H₃,
  unfold up_bounds at H₃,
  apply H₃, assumption,
end

lemma le_of_le_add_eps : ∀ (x y : ℝ),
  (∀ ε > 0, y ≤ x + ε) → y ≤ x
:= begin
  intros x y, contrapose!, intros H₁, use ((y-x)/2), split; linarith
end

example : ∀ (x y : ℝ), (∀ ε > 0, y ≤ x + ε) → y ≤ x
:= begin
  intros x y, contrapose!, intros H₁,
  exact ⟨(y-x)/2, by linarith, by linarith⟩,
end

example : ∀ (x y : ℝ), (∀ ε > 0, y ≤ x + ε) → y ≤ x
:= by { intros x y, contrapose!, intros H₁, exact ⟨(y-x)/2, by linarith, by linarith⟩}

example : ∀ (x y : ℝ), (∀ ε > 0, y ≤ x + ε) → y ≤ x
:= begin
  intros x y H₁,
  by_contradiction H₂,
  push_neg at H₂,
  have H₃ := calc
    y    ≤ x + (y-x)/2 : by { apply H₁, linarith }
    ...  = x/2 + y/2   : by ring
    ...  < y           : by linarith,
  linarith
end

local notation `|`x`|` := abs x

def limit (u : ℕ → ℝ) (l : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

