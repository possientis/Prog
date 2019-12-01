variables (a b c d e : ℕ)
variable h1 : a = b
variable h2 : b = c + 1
variable h3 : c = d
variable h4 : e = 1 + d

lemma L1 : a = e
:= calc
  a   = b     : h1
  ... = c + 1 : h2
  ... = d + 1 : h3 ▸ rfl
  ... = 1 + d : add_comm _ _
  ... = e     : eq.symm h4

#check L1

include h1 h2 h3 h4
lemma L2 : a = e
:= calc
  a   = b     : by rw h1
  ... = c + 1 : by rw h2
  ... = d + 1 : by rw h3
  ... = 1 + d : by rw add_comm
  ... = e     : by rw h4

#check L2


lemma L3 : a = e
:= calc
  a   = d + 1 : by rw [h1,h2,h3]
  ... = 1 + d : by rw add_comm
  ... = e     : by rw h4


#check L3

lemma L4 : a = e := by rw [h1, h2, h3, add_comm, h4]

#check L4

lemma L5 : a = e := by simp [h1, h2, h3, h4]

#check L5


lemma L6 : ∀ (x y z t : ℕ), x = y → y ≤ z → z + 1 < t → x < t
:= assume x y z t p q r, show x < t, from
calc
  x   = y     : p
  ... < y + 1 : nat.lt_succ_self y
  ... ≤ z + 1 : nat.succ_le_succ q
  ... < t     : r

#check L6

lemma L7 : ∀ (x y : ℕ), (x + y)*(x + y) = x * x + y * x + x * y + y * y
:= assume x y, calc
  (x + y) * (x + y) = (x + y) * x + (x + y) * y       : by rw mul_add
  ...               = x * x + y * x + (x + y) * y     : by rw add_mul
  ...               = x * x + y * x + (x * y + y * y) : by rw add_mul
  ...               = x * x + y * x + x * y + y * y   : by rw ←add_assoc -- \l

#check L7

lemma L8 : ∀ (x y : ℕ), (x + y)*(x + y) = x * x + y * x + x * y + y * y
  := assume x y, by rw [mul_add, add_mul, add_mul, ←add_assoc]

#check L8

lemma L9 : ∀ (x y : ℕ), (x + y)*(x + y) = x * x + y * x + x * y + y * y
  := assume x y, by simp [mul_add, add_mul]


#check L9
