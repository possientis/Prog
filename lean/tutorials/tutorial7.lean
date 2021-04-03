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

example : ∀ (P Q:Prop), (P ∨ Q) → ¬(P ∧ Q) → (¬ P ↔ Q) :=
begin
  intros P Q H₁ H₂, split; intros H₃,
    { cases H₁ with H₁ H₄,
      { exfalso, apply H₃, assumption},
      { assumption }},
    { intros H₄, apply H₂, split; assumption }
end

example : ∀ (u : ℕ → ℝ) (l l' : ℝ),
  seq_limit u l → seq_limit u l' → l = l' :=
begin
  intros u l l' H₁ H₂, by_contradiction H₃,
  change l ≠ l' at H₃, -- superfluous
  have H₄ : |l - l'| > 0,
    {apply abs_pos.mpr, apply sub_ne_zero_of_ne, assumption },
    specialize H₁ (|l - l'|/4) (by linarith), cases H₁ with N₁ H₁,
    specialize H₂ (|l - l'|/4) (by linarith), cases H₂ with N₂ H₂,
    let N := max N₁ N₂,
    specialize H₁ N (by apply le_max_left),
    specialize H₂ N (by apply le_max_right),
  have H₅ : |l - l'| < |l - l'|,
    calc
      |l - l'| = |(l - u N) + (u N - l')| : by ring
        ...    ≤ |l - u N| + |u N - l'|   : by apply abs_add
        ...    = |u N - l| + |u N - l'|   : by rw abs_sub
        ...    ≤ |l - l'|/4 + |u N - l'|  : by linarith
        ...    ≤ |l - l'|/4 + |l - l'|/4  : by linarith
        ...    = |l - l'|/2               : by ring
        ...    < |l -l'|                  : by linarith,
  linarith
end

example : ∀ (P Q : Prop), (¬Q → ¬P) → P → Q :=
begin
  intros P Q H₁ H₂, by_contradiction H₃,
  apply H₁; assumption
end

example : ∀ (P Q : Prop), (¬Q → ¬P) → P → Q :=
begin
  intros P Q H₁, contrapose, assumption
end
