open nat  -- zero_lt_succ

lemma L1 : ∃ (n : ℕ), n > 0
  :=  exists.intro 1
    (show 1 > 0, from zero_lt_succ 0)

lemma L2 : ∃ (n : ℕ), n > 0
  := have H : 1 > 0, from zero_lt_succ 0, -- assert (1 > 0) as H in Coq
    exists.intro 1 H

lemma L3 : ∃ (n : ℕ), n > 0
  := ⟨1, zero_lt_succ 0⟩

lemma L4 : ∀ (n : ℕ), n > 0 → ∃ (m : ℕ), m < n
  := assume n H, exists.intro 0 H

lemma L5 : ∀ (n : ℕ), n > 0 → ∃ (m : ℕ), m < n
  := assume n H, ⟨0,H⟩

lemma L6 : ∀ (n m p : ℕ), n < m → m < p → ∃ (q : ℕ), n < q ∧ q < p
  := assume n m p H1 H2, exists.intro m (and.intro H1 H2)

lemma L7 : ∀ (n m p : ℕ), n < m → m < p → ∃ (q : ℕ), n < q ∧ q < p
  := assume n m p H1 H2, ⟨m, H1, H2⟩

--#check @exists.intro
--#check @zero_lt_succ

--#check L1
--#check L2
--#check L3
--#check L4
--#check L5
--#check L6
--#check L7

variable g : ℕ → ℕ → ℕ
variable Hg : g 0 0 = 0

theorem T1 : ∃ (n : ℕ), g n n = n := ⟨0,Hg⟩
theorem T2 : ∃ (n : ℕ), g n 0 = n := ⟨0,Hg⟩
theorem T3 : ∃ (n : ℕ), g 0 0 = n := ⟨0,Hg⟩
theorem T4 : ∃ (n : ℕ), g n n = 0 := ⟨0,Hg⟩

--#check T1
--#check T2
--#check T3
--#check T4

set_option pp.implicit true -- display implicit arguments
--#print T1
--#print T2
--#print T3
--#print T4

--#check @exists.elim

lemma L8 : ∀ (α : Type) (p q : α → Prop), (∃ (x : α), p x ∧ q x) → ∃ (x : α), q x ∧ p x
  :=  assume α p q H,
      show ∃ (x : α), q x ∧ p x,
        from exists.elim H
        (assume x H, exists.intro x
          (show q x ∧ p x, from ⟨H.right,H.left⟩))

--#check L8

lemma L9 : ∀ (α : Type) (p q : α → Prop), (∃ (x : α), p x ∧ q x) → ∃ (x : α), q x ∧ p x
  :=  assume α p q H,
      show ∃ (x : α), q x ∧ p x,
        from exists.elim H
        (assume x H,⟨x,H.right,H.left⟩)


--#check L9


lemma L10 : ∀ (α : Type) (p q : α → Prop), (∃ (x : α), p x ∧ q x) → ∃ (x : α), q x ∧ p x
  := assume α p q H,
    match H with ⟨x,H⟩
      := ⟨x,H.right,H.left⟩
    end

--#check L10

lemma L11 : ∀ (α : Type) (p q : α → Prop), (∃ (x : α), p x ∧ q x) → ∃ (x : α), q x ∧ p x
  := assume α p q H,
    match H with ⟨(x:α),(H:p x ∧ q x)⟩
      := ⟨x,H.right,H.left⟩
    end

--#check L11

lemma L12 : ∀ (α : Type) (p q : α → Prop), (∃ (x : α), p x ∧ q x) → ∃ (x : α), q x ∧ p x
  := assume α p q H,
    match H with ⟨x, H1, H2⟩
      := ⟨x,H2,H1⟩
    end

--#check L12


lemma L13 : ∀ (α : Type) (p q : α → Prop), (∃ (x : α), p x ∧ q x) → ∃ (x : α), q x ∧ p x
  := assume α p q H,
    let ⟨x,H1,H2⟩ := H in ⟨x,H2,H1⟩

--#check L13

lemma L14 : ∀ (α : Type) (p q : α → Prop), (∃ (x : α), p x ∧ q x) → ∃ (x : α), q x ∧ p x
  := assume α p q ⟨x,H1,H2⟩, ⟨x,H2,H1⟩

--#check L14

def is_even (n : ℕ) : Prop := ∃ (m : ℕ), n = 2 * m

lemma L15 : ∀ (n m : ℕ), is_even n → is_even m → is_even (n + m)
  := assume n m ⟨k,H⟩ ⟨k',H'⟩, ⟨k + k',
     show n + m = 2 * (k + k'),
     from calc
     n + m = 2 * k + m      : by rw H
     ...   = 2 * k + 2 * k' : by rw H' 
     ...   = 2 * (k + k')   : by rw mul_add
     ⟩

--#check L15

lemma L16 : ∀ (n m : ℕ), is_even n → is_even m → is_even (n + m)
  := assume n m ⟨k,H⟩ ⟨k',H'⟩, ⟨k + k', by rw [H, H', mul_add]⟩

--#check L16
