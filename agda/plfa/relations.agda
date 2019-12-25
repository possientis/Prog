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
