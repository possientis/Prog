import Stmt
import Subst
import Hoare

def Swap : Stmt :=
  "t" :== x ;;
  "x" :== y ;;
  "y" :== aVar "t"

def p₁(n m:ℕ) : Pred := λ s, s "x" = n ∧ s "y" = m

def p₂(n m:ℕ) : Pred := λ s, s "x" = m ∧ s "y" = n

def p₃(n m:ℕ) : Pred := λ s, s "t" = n ∧ s "y" = m

def p₄(n m:ℕ) : Pred := λ s, s "x" = m ∧ s "t" = n

lemma L0 : "y" = "t" = false :=
begin
  apply propext, split,
    { from dec_trivial },
    { intros H1, contradiction }
end


lemma L1 : ∀ (n m:ℕ), subst "t" x (p₃ n m) = p₁ n m :=
begin
  intros n m,
  unfold subst, unfold bindVar, unfold p₁, unfold p₃,
  unfold x, unfold aVar,
  apply funext, intros s, apply propext, split; intros H1; cases H1 with H1 H2,
    { simp at H1, cases decidable.em ("y" = "t") with H3 H3,
      { exfalso, revert H3, from dec_trivial},
      { simp [H3] at H2, split; assumption }},
    { split,
      { simp, assumption },
      { cases decidable.em ("y" = "t") with H3 H3,
        { exfalso, revert H3, from dec_trivial },
        { simp [H3], assumption }}}
end

lemma L2 : ∀ (n m:ℕ), subst "x" y (p₄ n m) = p₃ n m :=
begin
  intros n m,
  unfold subst, unfold bindVar, unfold p₃, unfold p₄, unfold y, unfold aVar,
  apply funext, intros s, apply propext, split; intros H1; cases H1 with H1 H2,
    { simp at H1, cases decidable.em ("t" = "x") with H3 H3,
      { exfalso, revert H3, from dec_trivial },
      { simp [H3] at H2, split; assumption }},
    {split,
      { simp, assumption },
      { cases decidable.em ("t" = "x") with H3 H3,
        { exfalso, revert H3, from dec_trivial },
        { simp [H3], assumption }}}
end

lemma Swap_Correct : ∀ (n m:ℕ), Hoare (p₁ n m) Swap (p₂ n m) :=
begin
  intros n m, unfold Swap, apply (seq_intro _ (p₃ n m)),
    { rw ← L1, apply assign_intro },
    { apply (seq_intro _ (p₄ n m)),
      { rw ← L2, apply assign_intro },
      {}}
end
