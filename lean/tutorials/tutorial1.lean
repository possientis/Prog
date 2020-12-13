import data.real.basic

example : ∀ (a b c : ℝ), (a * b) * c = b * (a * c) :=
begin
  intros a b c, rw (mul_comm a b), apply mul_assoc
end

example : ∀ (a b c : ℝ) , (c * b) * a = b * (a * c) :=
begin
  intros a b c,
  calc
  (c * b) * a   = (b * c)* a  : by rw (mul_comm c b)
  ...           =  b *(c * a) : by apply mul_assoc
  ...           =  b *(a * c) : by rw (mul_comm c a)
end

example : ∀ (a b c : ℝ), a * (b * c) = b * (a * c) :=
begin
  intros a b c,
  calc
  a * (b * c)   = (a * b)* c  : by rw mul_assoc
  ...           = (b * a)* c  : by rw (mul_comm a b)
  ...           =  b *(a * c) : by apply mul_assoc
end

example : ∀ (a b c d : ℝ),
  c = d*a + b →
  b = a*d     →
  c = 2*a*d   :=
begin
  intros a b c d H₁ H₂,
  calc
  c   = d*a + b       : H₁
  ... = d*a + a*d     : by rw H₂
  ... = a*d + a*d     : by rw (mul_comm d a)
  ... = 2*(a*d)       : by rw two_mul
  ... = 2*a*d         : by rw mul_assoc
end

example : ∀ (a b c d : ℝ),
  c = b*a - d  →
  d = a*b      →
  c = 0        :=
begin
  intros a b c d H₁ H₂,
  calc
  c   = b*a - d     : H₁
  ... = b*a - a*b   : by rw H₂
  ... = a*b - a*b   : by rw mul_comm
  ... = 0           : by apply sub_self
end


example : ∀ (a b c d : ℝ),
  c = d*a + b  →
  b = a*d      →
  c = 2*a*d    :=
begin
  intros a b c d H₁ H₂,
  calc
  c   = d*a + b     : H₁
  ... = d*a + a*d   : by rw H₂
  ... = 2*a*d       : by ring
end

example : ∀ (a b c : ℝ), a * (b * c) = b * (a * c) :=
begin
  intros a b c, ring
end

example : ∀ (a b : ℝ), (a + b) + a = 2*a + b :=
begin
  intros a b, ring
end

example : ∀ (a b : ℝ), (a + b)*(a - b) = a^2 - b^2 :=
begin
  intros a b,
  calc
  (a + b)*(a - b) = (a + b)*a - (a + b)*b       : by apply mul_sub
  ...             = a*a + b*a - (a + b)*b       : by rw add_mul
  ...             = a*a + b*a - (a*b + b*b)     : by rw add_mul
  ...             = a*a + (b*a - (a*b + b*b))   : by rw add_sub
  ...             = a*a + (b*a - a*b - b*b)     : by rw sub_sub
  ...             = a*a + (a*b - a*b - b*b)     : by rw (mul_comm b a)
  ...             = a*a + (0 - b*b)             : by rw sub_self
  ...             = a*a + 0 - b*b               : by rw add_sub
  ...             = a*a - b*b                   : by rw add_zero
  ...             = a^2 - b*b                   : by rw (pow_two a)
  ...             = a^2 - b^2                   : by rw (pow_two b)
end

example : ∀ (a b : ℝ), (a + b)*(a - b) = a^2 - b^2 :=
begin
  intros a b, ring
end
