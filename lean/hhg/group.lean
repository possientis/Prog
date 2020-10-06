inductive ℤ₂ : Type
| zero
| one

def ℤ₂.add : ℤ₂ → ℤ₂ → ℤ₂
| ℤ₂.zero  x       := x
| x        ℤ₂.zero := x
| ℤ₂.one   ℤ₂.one  := ℤ₂.zero

-- figure out what you need to provide to define an add_group instance
#print add_group

lemma ℤ₂.add_assoc : ∀ (x y z : ℤ₂), ℤ₂.add (ℤ₂.add x y) z = ℤ₂.add x (ℤ₂.add y z) :=
begin
  intros x y z, cases x; cases y; cases z; unfold ℤ₂.add
end

lemma ℤ₂.zero_add : ∀ (x : ℤ₂), ℤ₂.add ℤ₂.zero x = x :=
begin
  intros x, cases x; unfold ℤ₂.add
end

lemma ℤ₂.add_zero : ∀ (x : ℤ₂), ℤ₂.add x ℤ₂.zero = x :=
begin
  intros x, cases x; unfold ℤ₂.add
end

def ℤ₂.neg : ℤ₂ → ℤ₂
| x := x

lemma ℤ₂.add_left_neg : ∀ (x : ℤ₂), ℤ₂.add (ℤ₂.neg x) x = ℤ₂.zero :=
begin
  intros x, unfold ℤ₂.neg, cases x; unfold ℤ₂.add
end

@[instance] def ℤ₂.add_group : add_group ℤ₂ :=
  { add          := ℤ₂.add
  , add_assoc    := ℤ₂.add_assoc
  , zero         := ℤ₂.zero
  , zero_add     := ℤ₂.zero_add
  , add_zero     := ℤ₂.add_zero
  , neg          := ℤ₂.neg
  , add_left_neg := ℤ₂.add_left_neg
  }

lemma ℤ₂.L₁ : ∀ (x y z : ℤ₂), (x + y) + z = x + (y + z) :=
begin
  intros x y z, apply add_assoc
end

lemma ℤ₂.L₂ : ∀ (x : ℤ₂), 0 + x = x :=
begin
  intros x, apply zero_add
end

lemma ℤ₂.L₃ : ∀ (x : ℤ₂), x + 0 = x :=
begin
  intros x, apply add_zero
end

lemma ℤ₂.L₄ : ∀ (x : ℤ₂), (-x) + x = 0 :=
begin
  intros x, apply add_left_neg
end

def ℤ₂.mul : ℤ₂ → ℤ₂ → ℤ₂
| ℤ₂.one  x        := x
| x       ℤ₂.one   := x
| ℤ₂.zero ℤ₂.zero  := ℤ₂.zero

#print ring

lemma ℤ₂.add_comm : ∀ (a b : ℤ₂), a + b = b + a :=
begin
  intros x y, cases x; cases y; refl
end

lemma ℤ₂.mul_assoc : ∀ (x y z : ℤ₂),
  ℤ₂.mul (ℤ₂.mul x y) z = ℤ₂.mul x (ℤ₂.mul y z) :=
begin
  intros x y z, cases x; cases y; cases z; refl
end

lemma ℤ2.one_mul : ∀ (x : ℤ₂), ℤ₂.mul ℤ₂.one x = x :=
begin
  intros x, cases x; refl
end

lemma ℤ₂.mul_one : ∀ (x : ℤ₂), ℤ₂.mul x ℤ₂.one = x :=
begin
  intros x, cases x; refl
end

lemma ℤ₂.left_distrib : ∀ (x y z : ℤ₂),
  ℤ₂.mul z (x + y) = ℤ₂.mul z x + ℤ₂.mul z y :=
begin
  intros x y z, cases x; cases y; cases z; refl
end

lemma ℤ₂.right_distrib : ∀ (x y z : ℤ₂),
  ℤ₂.mul (x + y) z = ℤ₂.mul x z + ℤ₂.mul y z :=
begin
  intros x y z, cases x; cases y; cases z; refl
end

@[instance] def ℤ₂.ring : ring ℤ₂ :=
  { one      := ℤ₂.one
  , mul      := ℤ₂.mul
  , add_comm := ℤ₂.add_comm
  }
