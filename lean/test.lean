#check fun x : nat, x + 5
#check λ (x : ℕ), x + 5

constant α : Type
constant a : α

#reduce (λ x : α, x) a

#eval 12345 * 54321

def foo : (ℕ → ℕ) → ℕ := λ f, f 0

#check foo

#print foo

def foo' := λ f : ℕ → ℕ , f 0

def double (x:ℕ) : ℕ := x + x

#reduce double 3

def square (x:ℕ) : ℕ := x * x

def twice (f:ℕ → ℕ) (x:ℕ) : ℕ := f (f x)

#reduce twice double 3

def x := 3





