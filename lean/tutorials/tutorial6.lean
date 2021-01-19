import tuto_lib

variable {ϕ : ℕ → ℕ}

lemma id_le_extraction' : extraction ϕ → ∀ n, n ≤ ϕ n :=
begin
  intros H₁ n, induction n with n IH,
    { apply zero_le },
    { apply nat.succ_le_of_lt, calc
      n   ≤ ϕ n            : IH
      ... < ϕ (nat.succ n) : by { apply H₁, apply lt_add_one } }
end

lemma extraction_ge : extraction ϕ → ∀ N N', ∃ n ≥ N', ϕ n ≥ N :=
begin
  intros H₁ N N', use max N N', split; try { apply le_max_right },
  calc
    N   ≤ max N N'      : by { apply le_max_left }
    ... ≤ ϕ (max N N')  : by { apply id_le_extraction', assumption }
end

variables {u : ℕ → ℝ} {a l : ℝ}

lemma near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
begin
  sorry
end
