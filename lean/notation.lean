notation `[` a `**` b `]` := a * b + 1

def mul_square (a b : ℕ) := a * a * b * b


infix `<*>`:50 := mul_square

#reduce [2 ** 3]
#reduce [2**3]
#reduce 2 <*> 3
#reduce 2<*>3


namespace int

def dvd (m n : ℤ) : Prop := ∃ k, k * m = n

instance : has_dvd int := ⟨int.dvd⟩

@[simp]
theorem dvd_zero : ∀ (n:ℤ), dvd n 0 := assume n, ⟨0,by simp⟩

infix `|` := dvd

theorem dvd_intro : ∀ {m n : ℤ} (k : ℤ), k * m = n → (m | n) :=
  assume m n k H, ⟨k,H⟩




end int

open int

section mod_m
  parameter (m : ℤ)
  variables (a b c : ℤ)

  definition mod_equiv := (m | b - a)

  local infix ≡ := mod_equiv

  lemma mod_refl : a ≡ a := _
 
end mod_m
