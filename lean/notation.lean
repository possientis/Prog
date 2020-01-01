notation `[` a `**` b `]` := a * b + 1

def mul_square (a b : ℕ) := a * a * b * b


infix `<*>`:50 := mul_square

#reduce [2 ** 3]
#reduce [2**3]
#reduce 2 <*> 3
#reduce 2<*>3


variables a b : ℕ

#check [a ** b]


namespace int

def dvd (m n : ℤ) : Prop := ∃ k, k * m = n

instance : has_dvd int := ⟨int.dvd⟩

@[simp]
theorem dvd_zero : ∀ (n:ℤ), dvd n 0 := assume n, ⟨0,by simp⟩

theorem dvd_intro : ∀ {m n : ℤ} (k : ℤ), k * m = n → dvd m n :=
  assume m n k H, ⟨k,H⟩

end int

open int


