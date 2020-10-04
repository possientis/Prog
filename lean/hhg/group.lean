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
