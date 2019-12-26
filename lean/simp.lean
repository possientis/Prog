lemma L1 : ∀ (x y z : ℕ), (x + 0) * (0 + y * 1 + z * 0) = x * y :=
  assume x y z,
    begin
      simp
    end


#check L1


lemma L2 : ∀ (x y z : ℕ) (p : nat → Prop), p (x * y) → p ((x + 0) * (0 + y * 1 + z * 0)) :=
  assume x y z p H, by { simp, assumption }

#check L2
