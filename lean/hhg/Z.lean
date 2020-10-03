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
        n₁ + m₃ + m₂ = n₁ + (m₃ + m₂) : by apply add_assoc
        ...          = n₁ + (m₂ + m₃) : by rw (add_comm m₃ m₂)
        ...          = (n₁ + m₂) + m₃ : by rw add_assoc
        ...          = (m₁ + n₂) + m₃ : by rw H₁
        ...          = m₁ + (n₂ + m₃) : by apply add_assoc
        ...          = m₁ + (m₂ + n₃) : by rw H₂
        ...          = m₁ + (n₃ + m₂) : by rw (add_comm m₂ n₃)
        ...          = m₁ + n₃ + m₂   : by rw add_assoc
    end,
  apply L₂, assumption
end

lemma equiv_equiv : equivalence (equiv) :=
begin
  unfold equivalence, split,
    { apply equiv_refl },
    { split,
      { apply equiv_sym },
      { apply equiv_trans }}
end

-- A type together with an equivalence relation on it
@[instance] def Z_setoid : setoid (ℕ × ℕ) :=
  { r     := equiv
  , iseqv := equiv_equiv
  }

-- Just testing the builtin notation ≈ for setoid  \~~
lemma equiv_def : forall (x y:ℕ × ℕ), x ≈ y ↔ equiv x y :=
begin
  intros x y, split; intros H₁; assumption
end

def Z : Type := quotient Z_setoid

def Z.zero : Z := ⟦(0,0)⟧ -- \[[ , \]]

lemma zero_eq : ∀ (n:ℕ), Z.zero = ⟦(n,n)⟧ :=
begin
  intros n, unfold Z.zero, apply quotient.sound,
  rw equiv_def, unfold equiv, simp
end

def add_ (p q:ℕ × ℕ) : Z :=
begin
  cases p with n₁ m₁, cases q with n₂ m₂,
  exact ⟦(n₁ + n₂, m₁ + m₂)⟧
end

def Z.add : Z → Z → Z := quotient.lift₂ add_
begin
  intros a₁ a₂ a₁' a₂',
  cases a₁ with n₁ m₁, cases a₂ with n₂ m₂,
  cases a₁' with n₁' m₁', cases a₂' with n₂' m₂',
  intros H₁ H₂, unfold add_, apply quotient.sound,
  rw equiv_def, unfold equiv, simp,
  rw equiv_def at H₁, unfold equiv at H₁, simp at H₁,
  rw equiv_def at H₂, unfold equiv at H₂, simp at H₂,
  by calc
  n₁ + (n₂ + (m₁' + m₂')) = n₁ + (n₂ + m₁' + m₂')   : by rw add_assoc
  ...                     = n₁ + (m₁' + n₂ + m₂')   : by rw (add_comm n₂)
  ...                     = n₁ + (m₁' + (n₂ + m₂')) : by rw add_assoc
  ...                     = (n₁ + m₁') + (n₂ + m₂') : by rw add_assoc
  ...                     = (m₁ + n₁') + (n₂ + m₂') : by rw H₁
  ...                     = (m₁ + n₁') + (m₂ + n₂') : by rw H₂
  ...                     = m₁ + (n₁' + (m₂ + n₂')) : by rw add_assoc
  ...                     = m₁ + (n₁' + m₂ + n₂')   : by rw add_assoc
  ...                     = m₁ + (m₂ + n₁' + n₂')   : by rw (add_comm n₁')
  ...                     = m₁ + (m₂ + (n₁' + n₂')) : by rw add_assoc
end

-- why is local required here ?
local infixl `⊕` : 50 := Z.add

local notation 0 := ⟦(0,0)⟧

lemma Z.add_def : ∀ (n₁ m₁ n₂ m₂ : ℕ),
  ⟦(n₁,m₁)⟧ ⊕ ⟦(n₂,m₂)⟧ = ⟦(n₁ + n₂, m₁ + m₂)⟧ :=
begin
  intros n₁ m₁ n₂ m₂, refl
end

lemma Z.add_0_n : ∀ (n:Z), 0 ⊕ n = n :=
begin
  intros n, apply quotient.induction_on n, clear n,
  intros p, cases p with n m, rw Z.add_def, simp
end
