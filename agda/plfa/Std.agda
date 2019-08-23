open import Data.Nat using (ℕ ; zero; suc; _+_; _*_; _^_; _∸_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)


+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p    = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)

n-+-0 : ∀ (n : ℕ) → n ≡ n + 0
n-+-0 zero    = refl
n-+-0 (suc n) = cong suc (n-+-0 n)

n-+-suc : ∀ (n m : ℕ) → suc n + m ≡ n + suc m
n-+-suc zero m    = refl
n-+-suc (suc n) m = cong suc (n-+-suc n m)

+-comm : ∀ (n m : ℕ) → n + m ≡ m + n
+-comm zero m    = n-+-0 m
+-comm (suc n) m = trans (cong suc (+-comm n m)) (n-+-suc m n)

data _≤_ : ℕ → ℕ → Set where
  z≤n : {n : ℕ} → zero ≤ n
  s≤s : {n m : ℕ} → n ≤ m → suc n ≤ suc m

Lemma1 : 2 ≤ 4
Lemma1 = s≤s (s≤s z≤n)

≤-refl : ∀ {n : ℕ} → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-inv : ∀ {n m : ℕ} → suc n ≤ suc m → n ≤ m
≤-inv (s≤s p) = p

≤-trans : ∀ {n m p} → n ≤ m → m ≤ p → n ≤ p
≤-trans z≤n q = z≤n
≤-trans (s≤s p) (s≤s q) = s≤s (≤-trans p q)

≤-antisym : ∀ {n m : ℕ} → n ≤ m → m ≤ n → n ≡ m
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s p) (s≤s q) = cong suc (≤-antisym p q)

-- we haven't defined 'or' yet
data Total (n m : ℕ) : Set where
  forward : n ≤ m → Total n m
  flipped : m ≤ n → Total n m


≤-total : ∀{n m : ℕ} → Total n m
≤-total {zero} {m}  = forward z≤n
≤-total {suc n} {zero} = flipped z≤n
≤-total {suc n} {suc m} = s-total ≤-total
  where 
  s-total : ∀ {n m : ℕ} → Total n m → Total (suc n) (suc m)
  s-total (forward p) = forward (s≤s p)
  s-total (flipped p) = flipped (s≤s p)

≤-total' : ∀{n m : ℕ} → Total n m
≤-total' {zero} {m}  = forward z≤n
≤-total' {suc n} {zero} = flipped z≤n
≤-total' {suc n} {suc m} with ≤-total' {n} {m}
≤-total' {suc n} {suc m} | forward p  = forward (s≤s p)
≤-total' {suc n} {suc m} | flipped p  = flipped (s≤s p)

