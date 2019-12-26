import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
      -----------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n


_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

infix 4 _≤_             -- binds less tightly than _+_

_ : 1 + 2 ≤ 3           -- no paranthesis needed
_ = s≤s (s≤s (s≤s z≤n)) -- way more verbose than coq's le_n

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n

inv-s≤s (s≤s m≤n) = m≤n


inv-z≤n : ∀ {n : ℕ}
  → n ≤ zero
    --------
  → n ≡ zero

inv-z≤n z≤n = refl


≤-refl : ∀ {n : ℕ}
    ---------
  → n ≤ n

≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
  ----------
  → m ≤ p

≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)


≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
  ----------
  → m ≡ n

≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)


data Total (m n : ℕ) : Set where

  forward :
      m ≤ n
      ---------
    → Total m n

  flipped :
      n ≤ m
      ---------
    → Total m n


data Total' : ℕ → ℕ → Set where

  forward' : ∀ {m n : ℕ}
    →  m ≤ n
      ---------
    → Total' m n

  flipped' : ∀ {m n : ℕ}
    →  n ≤ m
    ---------
    → Total' m n


≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
≤-total (suc m) (suc n) | forward m≤n = forward (s≤s m≤n)
≤-total (suc m) (suc n) | flipped n≤m = flipped (s≤s n≤m)


≤-total' : ∀ (m n : ℕ) → Total m n
≤-total' zero n = forward z≤n
≤-total' (suc m) zero = flipped z≤n
≤-total' (suc m) (suc n) = helper (≤-total' m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n) = forward (s≤s m≤n)
  helper (flipped n≤m) = flipped (s≤s n≤m)




