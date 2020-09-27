open prod
open nat

def equiv (p q : ℕ × ℕ) : Prop := fst p + snd q = fst q + snd p


lemma L₁ : ∀ (n m:ℕ), succ n = succ m → n = m :=
begin
  intros n m H₁, cases H₁, refl
end

lemma L₂ : ∀ (n m p:ℕ), n + p = m + p → n = m :=
begin
  intros n m p, revert n m, induction p with p IH; intros n m H₁,
    { assumption },
    { apply IH, have H₂ : succ (n + p) = succ (m + p) := by assumption,
      apply L₁, assumption }
end

lemma equiv_refl : ∀ (p : ℕ × ℕ), equiv p p :=
begin
  unfold equiv, intros p, cases p with n m, simp
end

lemma equiv_sym : ∀ (p q : ℕ × ℕ), equiv p q → equiv q p :=
begin
  unfold equiv, intros p q, cases p with n m, cases q with n' m', simp,
  intros H1, symmetry, assumption
end

lemma equiv_trans : ∀ (p q r : ℕ × ℕ), equiv p q → equiv q r → equiv p r :=
begin
  intros p q r, cases p with n₁ m₁, cases q with n₂ m₂, cases r with n₃ m₃,
  unfold equiv, simp, intros H₁ H₂,
  have H₃ : (n₁ + m₃) + m₂ = (m₁ + n₃) + m₂ :=
    begin
      from calc
        n₁ + m₃ + m₂ = n₁ + m₂ + m₃ : _
        ...          = m₁ + n₃ + m₂ : _
    end,
  apply L₂, assumption
end

