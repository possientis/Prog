namespace hidden  -- avoiding conflict with library

def divides (m n : ℕ) : Prop := ∃ k, m * k = n

instance : has_dvd nat := ⟨divides⟩    -- for '|' notation ?

def even (n : ℕ) : Prop := divides 2 n  -- 2 | n fails

variables a b : ℕ

#check divides a b
#check a^b
#check even (a^b + 3)










end hidden
