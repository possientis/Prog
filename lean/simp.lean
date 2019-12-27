import init.data.list.basic
open list

lemma L1 : ∀ (x y z : ℕ), (x + 0) * (0 + y * 1 + z * 0) = x * y :=
  assume x y z,
    begin
      simp
    end


#check L1


lemma L2 : ∀ (x y z : ℕ) (p : nat → Prop), p (x * y) → p ((x + 0) * (0 + y * 1 + z * 0)) :=
  assume x y z p H, by { simp, assumption }

#check L2

/-
lemma L3 : ∀ (xs : list ℕ), reverse (xs ++ [1,2,3]) = [3,2,1] ++ reverse xs :=
  assume xs,
    begin
      simp
    end
 -/
 
local attribute [simp] mul_comm mul_assoc mul_left_comm
lemma L4 : ∀ (x y z w : ℕ), x * y + z * w * x = x * w * z + y * x :=
  assume x y z w,
    begin
      simp
    end

#check L4

#check @mul_left_comm
