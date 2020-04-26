namespace hidden1
inductive nat : Type
| zero : nat
| succ : nat → nat

open nat

--#check @nat.succ
--#check @nat.rec
--#check @nat.rec_on



def add2 (m n : nat) : nat :=
  nat.rec_on n m (λ n add_m_n, nat.succ add_m_n)

end hidden1

open nat

lemma L1 : ∀ (n : ℕ), 0 + n = n :=
  assume n,
    nat.rec_on n
      (show 0 + 0 = 0, from rfl)
      (assume m (IH : 0 + m = m),
        show 0 + succ m = succ m, from
          calc
            0 + succ m = succ (0 + m) : rfl
            ...        = succ m: by rw IH)

--#check L1

--#check add_succ

lemma L2 : ∀ (n : ℕ), 0 + n = n :=
  assume n, nat.rec_on n rfl (λ (n:ℕ) (p:0 + n = n), by rw [add_succ, p])

--#check L2

lemma L3 : ∀ (n : ℕ), 0 + n = n :=
  assume n, nat.rec_on n rfl (λ n IH, by simp only [add_succ, IH])

--#check L3

lemma L4 : ∀ (m n p : ℕ), (m + n) + p = m + (n + p) :=
  assume m n p, nat.rec_on p
    (by simp)
    (assume p IH, show (m + n) + succ p = m + (n + succ p), from
      calc
        (m + n) + succ p = succ ((m + n) + p) : by refl
                ...      = succ (m + (n + p)) : by rw [IH]
                ...      = m + succ (n + p)   : by refl
                ...      = m + (n + succ p)   : by refl)

--#check L4


lemma L5 : ∀ (m n : ℕ), succ m + n = succ (m + n) :=
  assume m n, nat.rec_on n
    (by refl)
    (assume n IH, show succ m + succ n = succ (m + succ n), from
      calc
        succ m + succ n = succ (succ m + n)     : by refl
               ...      = succ (succ (m + n))   : by rw IH
               ...      = succ (m + succ n)     : by refl)

--#check L5


lemma L6 : ∀ (m n : ℕ), m + n = n + m :=
  assume m n, nat.rec_on n
    (begin symmetry, apply L1 end)
    (assume n IH,
      show m + succ n = succ n + m, from
        calc
          m + succ n  = succ (m + n)  : by refl
              ...     = succ (n + m)  : by rw IH
              ...     = succ n + m    : symm (L5 n m))

--#check L6
