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

lemma le_lim : forall (x y : ℝ) (u : ℕ → ℝ),
  limit u x → (∀ n, y ≤ u n) → y ≤ x
:= begin
  intros x y u H₁ H₂,
  apply le_of_le_add_eps,
  intros ε H₃,
  cases H₁ ε H₃ with N H₄,
  calc
  y   ≤ u N           : H₂ N
  ... = x + (u N - x) : by linarith
  ... ≤ x + |u N - x| : add_le_add (by apply le_refl) (by apply le_abs_self)
  ... ≤ x + ε         : add_le_add (by apply le_refl) (H₄ N (by apply le_refl))
end

lemma inv_succ_pos : ∀ (n : ℕ), 1/(n+1 : ℝ) > 0
:=begin
  intros n,
  suffices : (n + 1 : ℝ) > 0 ,
    {exact one_div_pos.mpr this},
    {norm_cast, linarith}
end


lemma limit_inv_succ : ∀ (ε > 0), ∃ (N : ℕ), ∀ (n ≥ N), 1/(n + 1 : ℝ) ≤ ε
:=
begin
  intros ε H₁,
  suffices : ∃ N : ℕ, 1/ε ≤ N,
    { cases this with N H₂, use N, intros n H₃, rw div_le_iff,
      { rw ← div_le_iff',
        {replace H₃ : (N : ℝ) ≤ n,
          {exact_mod_cast H₃},
          {linarith}},
        {assumption}},
      {exact_mod_cast _, apply nat.succ_pos}},
    { apply archimedean_iff_nat_le.1, apply_instance }
end

--#check archimedean_iff_nat_le.1

lemma inf_seq : ∀ (A : set ℝ) (a : ℝ),
  (a is_an_inf_of A) ↔ (a ∈ low_bounds A ∧ ∃ u : ℕ → ℝ, limit u a ∧ ∀ n, u n ∈ A)
:=begin
  intros A a, split,
    { intros H₁, unfold is_inf at H₁, unfold is_max at H₁, cases H₁ with H₁ H₂, split,
      { assumption },
      { have H₃ : ∀ (n:ℕ), ∃ (x ∈ A), x < a + 1/(n+1),
          { intros n, apply inf_lt,
            { exact ⟨H₁,H₂⟩},
            { have : 0 < 1/(n + 1 : ℝ),
              {apply inv_succ_pos},
              linarith}},
        choose u H₄ using H₃,
        use u,
        split,
          { intros ε H₅, cases limit_inv_succ ε H₅ with N H₆,
            use N, intros n H₇,
            have : a ≤ u n,
              { unfold low_bounds at H₁,
                apply H₁, cases (H₄ n) with H₈ H₉, assumption },
            have := calc
              u n <  a + 1/(n + 1) : (H₄ n).2
              ... <= a + ε         : add_le_add (le_refl _) (H₆ n H₇),
            rw abs_of_nonneg; linarith},
          { intros n, exact (H₄ n).1}}},
    { intros H₁, rcases H₁ with ⟨H₁, u, H₂, H₃⟩,
      unfold is_inf, unfold is_max, split,
        { assumption },
        { unfold up_bounds, intros x H₄, unfold low_bounds at H₄,
          apply le_lim,
            { assumption },
            { intros n, apply H₄, apply H₃}}}
end


