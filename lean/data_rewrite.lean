universe u

example {α : Type u} [ring α] (a b c : α) :
  a * 0 + 0 * b + c * 0 + 0 * a = 0 :=
  begin
    rw [mul_zero, mul_zero, zero_mul, zero_mul],
    repeat { rw add_zero }
  end

def ex2 {α : Type u} [ring α] (a b c : α) :
  a * 0 + 0 * b + c * 0 + 0 * a = 0 :=
  begin
    rw [mul_zero, mul_zero, zero_mul, zero_mul],
    repeat { rw add_zero }
  end

#check @ex2

-- why is this failing ?
/-
lemma L1 : ∀ {α : Type u} [ring α] (a b c : α),
  a * 0 + 0 * b + c * 0 + 0 * a = 0 :=
-/

