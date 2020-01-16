namespace hidden1
inductive nat : Type
| zero : nat
| succ : nat → nat

open nat

#check @nat.succ
#check @nat.rec
#check @nat.rec_on



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

#check L1
