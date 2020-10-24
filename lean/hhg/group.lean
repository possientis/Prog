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

lemma ℤ₂.one_mul : ∀ (x : ℤ₂), ℤ₂.mul ℤ₂.one x = x :=
begin
  intros x, cases x; refl
end

lemma ℤ₂.mul_one : ∀ (x : ℤ₂), ℤ₂.mul x ℤ₂.one = x :=
begin
  intros x, cases x; refl
end

lemma ℤ₂.left_distrib : ∀ (x y z : ℤ₂),
  ℤ₂.mul x (y + z) = ℤ₂.mul x y + ℤ₂.mul x z :=
begin
  intros x y z, cases x; cases y; cases z; refl
end

lemma ℤ₂.right_distrib : ∀ (x y z : ℤ₂),
  ℤ₂.mul (x + y) z = ℤ₂.mul x z + ℤ₂.mul y z :=
begin
  intros x y z, cases x; cases y; cases z; refl
end

@[instance] def ℤ₂.ring : ring ℤ₂ :=
  { add            := ℤ₂.add
  , add_assoc      := ℤ₂.add_assoc
  , zero           := ℤ₂.zero
  , zero_add       := ℤ₂.zero_add
  , add_zero       := ℤ₂.add_zero
  , neg            := ℤ₂.neg
  , add_left_neg   := ℤ₂.add_left_neg
  , add_comm       := ℤ₂.add_comm
  , mul            := ℤ₂.mul
  , mul_assoc      := ℤ₂.mul_assoc
  , one            := ℤ₂.one
  , one_mul        := ℤ₂.one_mul
  , mul_one        := ℤ₂.mul_one
  , left_distrib   := ℤ₂.left_distrib
  , right_distrib  := ℤ₂.right_distrib
  }


#print field


def ℤ₂.inv : ℤ₂ → ℤ₂ := λ x, x

lemma ℤ₂.zero_ne_one : ℤ₂.zero ≠ ℤ₂.one :=
begin
  intros H₁, cases H₁
end

lemma ℤ₂.mul_inv_cancel : ∀ (x : ℤ₂), x ≠ 0 → x * ℤ₂.inv x = 1 :=
begin
  intros x H₁, cases x,
    { exfalso, apply H₁, refl },
    { refl }
end

lemma ℤ₂.inv_mul_cancel : ∀ (x : ℤ₂), x ≠ 0 → ℤ₂.inv x * x = 1 :=
begin
  intros x H₁, cases x,
    { exfalso, apply H₁, refl },
    { refl }
end

lemma ℤ₂.mul_comm : ∀ (x y : ℤ₂), x * y = y * x :=
begin
  intros x y, cases x; cases y; refl
end

@[instance] def ℤ₂.field : field ℤ₂ :=
  { add            := ℤ₂.add
  , add_assoc      := ℤ₂.add_assoc
  , zero           := ℤ₂.zero
  , zero_add       := ℤ₂.zero_add
  , add_zero       := ℤ₂.add_zero
  , neg            := ℤ₂.neg
  , add_left_neg   := ℤ₂.add_left_neg
  , add_comm       := ℤ₂.add_comm
  , mul            := ℤ₂.mul
  , mul_assoc      := ℤ₂.mul_assoc
  , one            := ℤ₂.one
  , one_mul        := ℤ₂.one_mul
  , mul_one        := ℤ₂.mul_one
  , left_distrib   := ℤ₂.left_distrib
  , right_distrib  := ℤ₂.right_distrib
  , inv            := ℤ₂.inv
  , zero_ne_one    := ℤ₂.zero_ne_one
  , mul_inv_cancel := ℤ₂.mul_inv_cancel
  , inv_mul_cancel := ℤ₂.inv_mul_cancel
  , mul_comm       := ℤ₂.mul_comm
  }

#reduce (1 : ℤ₂) * 0 / (0 - 1)

#reduce (3 : ℤ₂)

def ℤ₂.pow (x : ℤ₂) : ℕ → ℤ₂
| 0       := ℤ₂.one
| (n + 1) := x * ℤ₂.pow n


@[instance] def ℤ₂.has_pow : has_pow ℤ₂ ℕ :=
  { pow := ℤ₂.pow
  }


lemma ring_x_x : ∀ (x : ℤ₂), x + x = 2 * x :=
begin
  intros x, cases x; refl
end

lemma ring_xx : ∀ (x : ℤ₂), x*x = x^2 :=
begin
  intros x, cases x; refl
end

lemma ring_ex2 : ∀ (x y : ℤ₂),
  (x + y)^2 = x^2 + 2*x*y + y^2 :=
begin
  intros x y, calc
    (x + y)^2       = (x + y) * (x + y)            : by rw ring_xx
    ...             = x*(x + y) + y*(x + y)        : by rw right_distrib
    ...             = x*x + x*y + y*(x + y)        : by rw left_distrib
    ...             = x*x + x*y + (y*x + y*y)      : by rw left_distrib
    ...             = x*x + (x*y + (y*x + y*y))    : by rw add_assoc
    ...             = x*x + (x*y + y*x + y*y)      : by rw add_assoc
    ...             = x*x + (x*y + x*y + y*y)      : by rw (mul_comm y x)
    ...             = x*x + (2*(x*y) + y*y)        : by rw ring_x_x
    ...             = x*x + (2*x*y + y*y)          : by rw mul_assoc
    ...             = x*x + 2*x*y + y*y            : by rw add_assoc
    ...             = x^2 + 2*x*y + y*y            : by rw ring_xx
    ...             = x^2 + 2*x*y + y^2            : by rw ring_xx
end

lemma ring_ex3 : ∀ (x y : ℤ₂),
  (x + y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + x^3 :=
begin
  intros x y, calc
    (x + y)^3 = (x + y)*(x + y)^2                                     : by refl
    ...       = (x + y)*(x^2 + 2*x*y + y^2)                           : by rw ring_ex2
    ...       = x*(x^2 + 2*x*y + y^2) + y*(x^2 + 2*x*y + y^2)         : by rw right_distrib
    ...       = (x*(x^2 + (2*x*y)) + x*y^2) + y*(x^2 + 2*x*y + y^2)   : by rw left_distrib
    ...       = (x*x^2 + x*(2*x*y) + x*y^2) + y*(x^2 + 2*x*y + y^2)   : by rw left_distrib
    ...       = (x^3 + x*(2*x*y) + x*y^2) + y*(x^2 + 2*x*y + y^2)     : by refl
    ...       = (x^3 + x*(2*x)*y + x*y^2) + y*(x^2 + 2*x*y + y^2)     : by rw (mul_assoc x (2*x) y)
    ...       = (x^3 + x*2*x*y + x*y^2) + y*(x^2 + 2*x*y + y^2)       : by rw (mul_assoc x 2 x)
    ...       = (x^3 + 2*x*x*y + x*y^2) + y*(x^2 + 2*x*y + y^2)       : by rw (mul_comm x 2)
    ...       = (x^3 + 2*(x*x)*y + x*y^2) + y*(x^2 + 2*x*y + y^2)     : by rw (mul_assoc 2 x x)
    ...       = (x^3 + 2*x^2*y + x*y^2) + y*(x^2 + 2*x*y + y^2)       : by rw ring_xx
    ...       = (x^3 + 2*x^2*y + x*y^2) + (y*(x^2 + 2*x*y) + y*y^2)   : by rw left_distrib
    ...       = (x^3 + 2*x^2*y + x*y^2) + (y*(x^2 + 2*x*y) + y^3)     : by refl
    ...       = (x^3 + 2*x^2*y + x*y^2) + (y*x^2 + y*(2*x*y) + y^3)   : by rw left_distrib
    ...       = (x^3 + 2*x^2*y + x*y^2) + (x^2*y + y*(2*x*y) + y^3)   : by rw (mul_comm y (x^2))
    ...       = (x^3 + 2*x^2*y + x*y^2) + (x^2*y + y*(2*x)*y + y^3)   : by rw (mul_assoc y (2*x) y)
    ...       = (x^3 + 2*x^2*y + x*y^2) + (x^2*y + y*2*x*y + y^3)     : by rw (mul_assoc y 2 x)
    ...       = (x^3 + 2*x^2*y + x*y^2) + (x^2*y + 2*y*x*y + y^3)     : by rw (mul_comm y 2)
    ...       = (x^3 + 2*x^2*y + x*y^2) + (x^2*y + 2*(y*x)*y + y^3)   : by rw (mul_assoc 2 y x)
    ...       = (x^3 + 2*x^2*y + x*y^2) + (x^2*y + 2*(x*y)*y + y^3)   : by rw (mul_comm y x)
    ...       = (x^3 + 2*x^2*y + x*y^2) + (x^2*y + 2*(x*y*y) + y^3)   : by rw (mul_assoc 2 (x*y) y)
    ...       = (x^3 + 2*x^2*y + x*y^2) + (x^2*y + 2*(x*(y*y)) + y^3) : by rw (mul_assoc x y y)
    ...       = (x^3 + 2*x^2*y + x*y^2) + (x^2*y + 2*(x*y^2) + y^3)   : by rw ring_xx
    ...       = (x^3 + 2*x^2*y + x*y^2) + (x^2*y + 2*x*y^2 + y^3)     : by rw (mul_assoc 2 x (y^2))
    ...       = x^3 + 2*x^2*y + x*y^2 + (x^2*y + 2*x*y^2) + y^3       : by rw (add_assoc (x^3 + 2*x^2*y + x*y^2))
    ...       = x^3 + 2*x^2*y + x*y^2 + x^2*y + 2*x*y^2 + y^3         : by rw (add_assoc (x^3 + 2*x^2*y + x*y^2) (x^2*y))
    ...       = x^3 + 3*x^2*y + 3*x*y^2 +x^3       : _
end

