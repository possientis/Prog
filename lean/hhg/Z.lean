open prod

def equiv (p q : ℕ × ℕ) : Prop := fst p + snd q = fst q + snd p

lemma equiv_refl : ∀ (p : ℕ × ℕ), equiv p p :=
begin
  unfold equiv, intros p, cases p with n m, simp
end

lemma equiv_sym : ∀ (p q : ℕ × ℕ), equiv p q → equiv q p :=
begin
  unfold equiv, intros p q, cases p with n m, cases q with n' m', simp,
  intros H1, symmetry, assumption
end
