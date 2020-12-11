import data.real.basic

example : ∀ (a b c : ℝ), (a * b) * c = b * (a * c) :=
begin
  intros a b c, rw (mul_comm a b), apply mul_assoc
end
