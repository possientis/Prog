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


lemma L5 : ∀ (x y z w : ℕ) (p : ℕ → Prop),
  p (x * y + z * w * x) → p (x * w * z + y * x) :=
    assume x y z w p H,
      begin
        simp, simp at H, assumption
      end

#check L5


variables {α : Type} [comm_ring α]

lemma L6 : ∀ (x y z:α), (x - x) * y + z  = z :=
  assume x y z,
    begin
      simp
    end

#check @L6


lemma L7 : ∀ (x y z w:α), x * y + z * w * x = x * w * z + y * x :=
  assume x y z w,
    begin
      simp
    end

#check @L7


def f (m n : ℕ) : ℕ := m + n + m


lemma L8 : ∀ {m n : ℕ}, n = 1 → 0 = m → (f m n) * m = m :=
  assume m n H1 H2,
    begin
      simp [f, H2.symm]
    end

#check @L8

lemma L9 : ∀ (f : ℕ → ℕ) (k : ℕ), f 0 = 0 → k = 0 → f k = 0 :=
  assume f k H1 H2,
    begin
      simp [H2, H1]
    end

#check L9

lemma L10 : ∀ (f : ℕ → ℕ) (k : ℕ), f 0 = 0 → k = 0 → f k = 0 :=
  assume f k H1 H2,
    begin
      simp *
    end

#check L10


lemma L11 : ∀ (u w x y z : ℕ), x = y + z → w = u + x → w = z + y + u :=
  assume u w x y z H1 H2, by simp *

#check L11

lemma L12 : ∀ (p q : Prop), p → (p ∧ q <-> q) :=
  assume p q Hp, by simp *

#check L12


lemma L13 : ∀ (p q : Prop), p → p ∨ q := assume p q H, by simp *

#check L13

lemma L14 : ∀ (p q r : Prop), p → q → p ∧ (q ∨ r) :=
  assume p q r Hp Hq, by simp *

#check L14

lemma L15 : ∀ (x x' y y' : ℕ),
  x + 0 = x' → y + 0 = y' → x + y + 0 = x' + y' :=
    assume x x' y y' Hx Hy,
      begin
        simp at Hx, simp at Hy, simp *
      end

#check L15
