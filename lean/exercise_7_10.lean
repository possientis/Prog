namespace hidden

def prod (n : ℕ) : ℕ → ℕ :=
  nat.rec_on n (λ m, 0) (λ n prod_n, λ m, m + prod_n m)

def pred (n : ℕ) : ℕ :=
  nat.rec_on n 0 (λ n pred_n, n)

def sub (n m : ℕ) : ℕ :=
  nat.rec_on m n (λ m sub_n_m, pred (sub_n_m))

def exp (n m : ℕ) : ℕ :=
  nat.rec_on m 1 (λ m exp_n_m, n * exp_n_m)

#reduce exp 10 0
#reduce exp 10 1
#reduce exp 10 2
#reduce exp 10 3


end hidden
