lemma L1 : ∀ (p q:Prop), p → q → p ∧ q ∧ p :=
  assume p q hp hq,
    begin
      apply and.intro,
      exact hp,
      apply and.intro,
      exact hq,
      exact hp
    end

#check L1
#print L1

lemma L2 : ∀ (p q:Prop), p → q → p ∧ q ∧ p :=
  assume p q hp hq,
    begin
      apply and.intro hp,
      exact and.intro hq hp
    end

#print L2


lemma L3 : ∀ (p q:Prop), p → q → p ∧ q ∧ p :=
  assume p q hp hq,
    begin
      apply and.intro hp;     -- semi-colon is fine too
      exact and.intro hq hp
    end

lemma L4 : ∀ (p q:Prop), p → q → p ∧ q ∧ p :=
  assume p q hp hq,
    by exact and.intro hp (and.intro hq hp)


variables {p q : Prop} (hp : p) (hq : q)

include hp hq    -- bring those into context needed for proof

example : p ∧ q ∧ p :=
  begin
    apply and.intro hp,
    exact and.intro hq hp
  end

omit hp hq      -- cancels previous 'include' directive

lemma L5 : ∀ (p q r : Prop), p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  assume p q r,
    begin
      split,
        intro H,
        cases (and.right H) with Hq Hr,
            left,
            split,
              exact and.left H,
              assumption,
            right,
            split,
              exact and.left H,
              assumption,
        intro H,
        cases H with H' H',
            split,
            exact and.left H',
            left,
            exact and.right H',
          split,
            exact and.left H',
            right,
            cases H',
            intros,
            assumption
    end

#check L5


lemma L6 : ∀ (α:Type), α → α :=
  begin
    intro α,
    intro x,
    exact x
  end

#check L6

lemma L7 : ∀ (α:Type) (x:α), x = x :=
  begin
    intros α x,
    exact eq.refl x
  end


#check L7

lemma L8 : ∀ (m n p : ℕ), m = n → m = p → p = n :=
  begin
    intros n m p H1 H2,
    apply eq.trans,
      apply eq.symm,
        assumption,
      assumption
  end

#check L8

lemma L9 : ∀ (m n p q : ℕ), m = n → n = p → p = q → m = q :=
  begin
    intros m n p q H1 H2 H3,
    apply eq.trans,
      assumption,
      apply eq.trans; assumption
  end

#check L9


lemma L10 : ∀ (n:ℕ), (λ x:ℕ, 0) 0 = 0 :=
  begin
    intro n,
    refl
  end

#check L10


lemma L11 : ∀ (m n p : ℕ), m = n → m = p → p = n :=
  begin
    intros n m p H1 H2,
    transitivity,
      symmetry; assumption,
      assumption
  end

#check L11


lemma L12 : ∀ (n : ℕ), n ≤ n :=
  begin
    intros n,
    refl
  end

#check L12


lemma L13 : ∃ (n : ℕ), 5 = n :=
  begin
    apply exists.intro,
    refl
  end

#check L13


lemma L14 : ∃ (n : ℕ), 5 = n :=
  begin
    fapply exists.intro,  -- changes the order of subgoals
    exact 5,
    refl
  end

#check L14


lemma L15 : 3 = 3 :=
  begin
    generalize : 3 = x,
    revert x,
    intro y, reflexivity
  end

lemma L16 : 2 + 3 = 5 :=
  begin
    generalize H : 3 = x,
    rw ←H
  end

#check L15



lemma L17 : ∀ (p q:Prop), p ∨ q → q ∨ p :=
  begin
    intros p q H,
    cases H with Hp Hq,
     right, assumption,
     left, assumption
  end

lemma L18 : ∀ (p q:Prop), p ∧ q → q ∧ p :=
  begin
    intros p q H,
    cases H with Hp Hq,
    split; assumption
  end

lemma L19 : ∀ (p q r:Prop), p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  begin
    intros p q r,
    split; intros H,
      cases H with Hp Hqr,
        cases Hqr with Hq Hr,
          left, split; assumption,
          right, split; assumption,
      cases H with H H,
        cases H with Hp Hq,
          split,
            assumption,
            left, assumption,
        cases H with Hp Hr,
          split,
            assumption,
            right, assumption
  end

#check L19


lemma L20 : ∀ (p q : ℕ → Prop), (∃ x, p x) → ∃ x, p x ∨ q x :=
  begin
    intros p q H,
    cases H with x H,
    constructor,
    left, assumption
  end
