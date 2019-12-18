import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_;_∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_) -- \.-

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ = begin
  (3 + 4) + 5
  ≡⟨⟩
  7 + 5
  ≡⟨⟩
  12
  ≡⟨⟩
  3 + 9
  ≡⟨⟩
  3 + (4 + 5)
  ∎

-- identifiers cannot contain @.(){};_
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
    ≡⟨⟩
    n + p
    ≡⟨⟩
    zero + (n + p)
    ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
    ≡⟨⟩
    suc (m + n) + p
    ≡⟨⟩
    suc ((m + n) + p)
    ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
    ≡⟨⟩
    suc m + (n + p)
    ∎

+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p)
+-assoc-2 n p =
  begin
    (2 + n) + p
    ≡⟨⟩
    suc (1 + n) + p
    ≡⟨⟩
    suc ((1 + n) + p)
    ≡⟨ cong suc (+-assoc-1 n p) ⟩
    suc (1 + (n + p))
    ≡⟨⟩
    2 + (n + p)
    ∎
    where
    +-assoc-1 : ∀ (n p : ℕ) → (1 + n) + p ≡ 1 + (n + p)
    +-assoc-1 n p =
      begin
        (1 + n) + p
        ≡⟨⟩
        suc (0 + n) + p
        ≡⟨⟩
        suc ((0 + n) + p)
        ≡⟨ cong suc (+-assoc-0 n p) ⟩ 
        suc (0 + (n + p))
        ≡⟨⟩
        1 + (n + p)
        ∎
        where
        +-assoc-0 : ∀ (n p : ℕ) → (0 + n) + p ≡ 0 + (n + p)
        +-assoc-0 n p =
          begin
            (0 + n) + p
            ≡⟨⟩
            n + p
            ≡⟨⟩
            0 + (n + p)
            ∎

+-assoc' : (m : ℕ) → (n : ℕ) → (p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' = +-assoc

+-identity-r : ∀ (m : ℕ) → m + zero ≡ m
+-identity-r zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
    ∎
+-identity-r (suc m) =
  begin
    suc m + zero
    ≡⟨⟩
    suc (m + zero)
    ≡⟨ cong suc (+-identity-r m) ⟩
    suc m
    ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
    ≡⟨⟩
    suc n
    ≡⟨⟩
    suc (zero + n)
    ∎
+-suc (suc m) n =
  begin
    suc m + suc n
    ≡⟨⟩
    suc (m + suc n)
    ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
    ≡⟨⟩
    suc (suc m + n)
    ∎
