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

lemma extraction_tendsto_inf : extraction ϕ → ∀ N', ∃ N, ∀ n ≥ N, ϕ n ≥ N' :=
begin
  intros H₁ N', use N', intros n H₂, calc
    ϕ n   ≥ n           : by { apply id_le_extraction', assumption }
    ...   ≥ N'          : by assumption
end

variables {u : ℕ → ℝ} {a l : ℝ}

lemma near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
begin
  intros H₁ ε H₂ N, rcases H₁ with ⟨ϕ,H₁,H₃⟩,
  specialize H₃ ε H₂, cases H₃ with N₁ H₃,
  have H₄ : ∃ n ≥ N₁, ϕ n ≥ N, { apply extraction_ge, assumption },
  rcases H₄ with ⟨n,H₄,H₅⟩,
  use (ϕ n), split; try { assumption }, apply H₃, assumption
end

lemma subseq_tendsto_of_tendsto' :
  seq_limit u l       →
  extraction ϕ        →
  seq_limit (u ∘ ϕ) l :=
begin
  intros H₁ H₂ ε H₃, specialize H₁ ε H₃, cases H₁ with N₁ H₁,
  have H₄ : ∃ N, ∀ n, n ≥ N → ϕ n ≥ N₁,
    { apply extraction_tendsto_inf, assumption },
  cases H₄ with N H₄,
  use N, intros n H₅, apply H₁, apply H₄, assumption
end

lemma cluster_limit : seq_limit u l → cluster_point u a → a = l :=
begin
  intros H₁ H₂, rcases H₂ with ⟨ϕ,H₂,H₃⟩,
  have H₄: seq_limit (u ∘ ϕ) l, { apply subseq_tendsto_of_tendsto; assumption },
  apply unique_limit; assumption
end

