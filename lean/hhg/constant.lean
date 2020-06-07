constants a b : ℤ
constant f : ℤ → ℤ
constant g : ℤ → ℤ → ℤ

--#check λ x : ℤ, g (f (g a x)) (g x b)
--#check λ x, g (f (g a x)) (g x b)

constant Trool : Type
constants Trool.true Trool.false Trool.maybe : Trool




