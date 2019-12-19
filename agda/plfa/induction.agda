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

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
    ≡⟨ +-identity-r m ⟩
    m
    ≡⟨⟩
    zero + m
    ∎
+-comm m (suc n) =
  begin
    m + (suc n)
    ≡⟨ +-suc m n ⟩
    suc (m + n)
    ≡⟨ cong suc (+-comm m n ) ⟩
    suc (n + m)
    ≡⟨⟩
    suc n + m
    ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
    ≡⟨ +-assoc m n (p + q)⟩
    m + (n + (p + q))
    ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
    ≡⟨ sym (+-assoc m (n + p) q) ⟩
    m + (n + p) + q
    ∎

+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero n p = refl
+-assoc' (suc m) n p rewrite +-assoc' m n p = refl

+-identity' : ∀ (n : ℕ) → n + zero ≡ n
+-identity' zero = refl
+-identity' (suc n) rewrite +-identity' n = refl

+-suc' : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc' zero n = refl
+-suc' (suc m) n rewrite +-suc' m n =  refl

+-comm' : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm' m zero rewrite +-identity' m = refl
+-comm' m (suc n) rewrite +-suc' m n | +-comm' m n = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
    ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p
    ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p
    ≡⟨ +-assoc n m p ⟩
    n + (m + p)
    ∎

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ m n p = {!!}
