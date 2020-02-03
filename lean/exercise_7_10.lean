namespace hidden

def prod (n : ℕ) : ℕ → ℕ :=
  nat.rec_on n (λ m, 0) (λ n prod_n, λ m, m + prod_n m)

def pred (n : ℕ) : ℕ :=
  nat.rec_on n 0 (λ n pred_n, n)

def sub (n m : ℕ) : ℕ :=
  nat.rec_on m n (λ m sub_n_m, pred (sub_n_m))

def exp (n m : ℕ) : ℕ :=
  nat.rec_on m 1 (λ m exp_n_m, n * exp_n_m)


lemma one_prod : ∀ (n : ℕ), prod 1 n = n :=
  assume n,
    calc
      prod 1 n  = n + prod 0 n : by refl
        ...     = n + 0        : by refl
        ...     = n            : by refl

open nat

lemma prod_one : ∀ (n : ℕ), prod n 1 = n :=
  assume n,
    begin
      induction n with n IH,
        {by refl},
        {from calc
          prod (succ n) 1 = 1 + prod n 1 : by refl
            ...           = 1 + n        : by rw IH
            ...           = succ n       : by simp
        }
    end

lemma add_prod : ∀ (n m p : ℕ), prod (n + m) p = prod n p + prod m p :=
  assume n,
    begin
      induction n with n IH,
        {from assume m p,
          calc
            prod (0 + m) p  = prod m p            : by rw zero_add
              ...           = 0 + prod m p        : by rw zero_add
              ...           = prod 0 p + prod m p : by refl},
        {from assume m p,
          calc
            prod (succ n + m) p = prod (succ (n + m)) p       : by rw succ_add
                 ...            = p + prod (n + m) p          : by refl
                 ...            = p + (prod n p + prod m p)   : by rw IH
                 ...            = (p + prod n p) + prod m p   : by rw add_assoc
                 ...            = prod (succ n) p + prod m p  : by refl }

    end

lemma prod_assoc : ∀ (n m p : ℕ), prod (prod n m) p = prod n (prod m p) :=
  assume n,
    begin
      induction n with n IH,
        {from assume m p,
          calc
            prod (prod 0 m) p = prod 0 p          : by refl
                 ...          = 0                 : by refl
                 ...          = prod 0 (prod m p) : by refl},

        {from assume m p,
          calc
            prod (prod (succ n) m) p  = prod (m + prod n m) p         : by refl
                 ...                  = prod m p + prod (prod n m) p  : by rw add_prod
                 ...                  = prod m p + prod n (prod m p)  : by rw IH
                 ...                  = prod (succ n)(prod m p)       : by refl}
    end

lemma prod_succ : ∀ (n m : ℕ), prod n (succ m) = n + prod n m :=
  assume n,
    begin
      induction n with n IH,
        {from assume m,
          calc
            prod 0 (succ m) = 0             : by refl
              ...           = 0 + 0         : by refl
              ...           = 0 + prod 0 m  : by refl},
        {from assume m,
          calc
            prod (succ n) (succ m)  = (succ m) + prod n (succ m)  : _
                 ...                = (succ m) + (n + prod n m)   : _
                 ...                = (succ m + n) + prod n m     : _
                 ...                = _                           : _
    end


#check one_prod
#check prod_one
#check add_prod
#check prod_assoc

end hidden
