namespace hidden  -- avoiding conflict with library

def divides (m n : ℕ) : Prop := ∃ k, m * k = n

instance : has_dvd nat := ⟨divides⟩    -- for '|' notation ?

def even (n : ℕ) : Prop := divides 2 n  -- 2 | n fails

def prime (n : ℕ) : Prop := ¬(n = 1) ∧ (∀ (m:ℕ), divides m n → m = 1 ∨ m = n)

def primes_infinite : Prop := ∀ (n:ℕ), ∃ (p:ℕ), n ≤ p ∧ prime p

def Fermat_prime (n : ℕ) : Prop := prime n ∧ ∃ (k:ℕ), n = 2^(2^k) + 1

def Fermat_primes_infinite : Prop := ∀ (n:ℕ), ∃ (p:ℕ), n ≤ p ∧ Fermat_prime n

def Golbach : Prop := ∀ (n:ℕ), 4 ≤ n ∧ even n → ∃(p q:ℕ), prime p ∧ prime q ∧ n = p + q

--#print primes_infinite

end hidden
