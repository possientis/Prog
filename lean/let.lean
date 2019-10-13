def foo := let a := ℕ in λ (x : a), x + 2

-- foo cannot be expressed as bar which does not type check

-- def bar := (λ a, λ (x : a), x + 2) ℕ
