variables (real : Type) [ordered_ring real]
variables (log exp : real → real)
variable log_exp_eq : ∀ x, log (exp x) = x
variable exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable exp_pos : ∀ x, exp x > 0
variable exp_add : ∀ x y, exp(x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

lemma L1 : ∀(x y z:real), exp (x + y + z) = exp x * exp y * exp z :=
  assume x y z, calc
    exp (x + y + z) = exp (x + y) * exp z     : by rw exp_add
    ...             = exp x * exp y * exp z   : by rw exp_add

#check L1

lemma L2 : ∀(x:real), x > 0 → exp (log x) = x :=
  assume x (H:x > 0), show exp(log x) = x, from exp_log_eq H

#check L2

lemma L3 : ∀ (x y:real), x > 0 → y > 0 → log (x * y) = log x + log y :=
  assume x y Hx Hy, calc
    log (x * y) = log (exp (log x) * y)           : by rw (exp_log_eq Hx)
    ...         = log (exp (log x) * exp (log y)) : by rw (exp_log_eq Hy)
    ...         = log (exp (log x + log y))       : by rw exp_add
    ...         = log x + log y                   : by rw log_exp_eq

#check L3

#check @sub_self

lemma L4 : ∀ (x : ℤ), x * 0 = 0 :=
  assume x, calc
    x * 0   = x * (1 - 1)   : by rw sub_self
    ...     = x * 1 - x * 1 : by rw mul_sub
    ...     = 0             : by rw sub_self

#check L4
