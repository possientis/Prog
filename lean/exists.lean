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

#check @exists.intro
#check @zero_lt_succ

#check L1
#check L2
#check L3
#check L4
#check L5
#check L6
#check L7

variable g : ℕ → ℕ → ℕ
variable Hg : g 0 0 = 0

theorem T1 : ∃ (n : ℕ), g n n = n := ⟨0,Hg⟩
theorem T2 : ∃ (n : ℕ), g n 0 = n := ⟨0,Hg⟩
theorem T3 : ∃ (n : ℕ), g 0 0 = n := ⟨0,Hg⟩
theorem T4 : ∃ (n : ℕ), g n n = 0 := ⟨0,Hg⟩

#check T1
#check T2
#check T3
#check T4

set_option pp.implicit true -- display implicit arguments
#print T1
#print T2
#print T3
#print T4


