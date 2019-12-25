lemma L1 : ∀ (f : ℕ → ℕ) (k : ℕ), f 0 = 0 → k = 0 → f k = 0 :=
  assume f k H1 H2,
    begin
      rw H2,
      rw H1
    end

#check L1

lemma L2 : ∀ (x y : ℕ) (p : nat → Prop) (q : Prop), (q → x = y) → p y → q → p x :=
  assume x y p q H1 H2 H3,
    begin
      rw H1; assumption
    end

#check L2


lemma L3 : ∀ (f : ℕ → ℕ) (a b : ℕ), a = b → f a = 0 → f b = 0 :=
  assume f a b H1 H2,
    begin
      rw [←H1, H2]
    end

lemma L4 : ∀ (a b c : ℕ), a + b + c = a + c + b :=
  assume a b c, by rw [add_assoc, add_comm b, ←add_assoc]

#check L4


lemma L5 : ∀ (a b c : ℕ), a + b + c = a + c + b :=
  assume a b c,
    begin
      rw [add_assoc, add_assoc, add_comm b]
    end

#check L5

lemma L6 : ∀ (a b c : ℕ), a + b + c = a + c + b :=
  assume a b c,
    begin
      rw [add_assoc, add_assoc, add_comm _ b]
    end

#check L6


lemma L7 : ∀ (f : ℕ → ℕ) (a : ℕ), a + 0 = 0 → f a = f 0 :=
  assume f a H,
    begin
      rw add_zero at H,
      rw H
    end

-- rewrite can be used for Set, not just Prop

universe u

def tuple (α : Type u) (n : ℕ) := { l : list α // list.length l = n}

#print tuple


def ex1 {α : Type u} (n : ℕ) (H:n = 0) (t:tuple α n) : tuple α 0 :=
  begin
    rw H at t, assumption
  end

#check @ex1

def ex2 {α : Type u} [ring α] (a b c : α) :
  a * 0 + 0 * b + c * 0 + 0 * a = 0 :=
    begin
    end
  _
