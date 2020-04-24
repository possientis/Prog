module induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_;_∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_) -- \.-

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

*-distrib-r-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-r-+ zero n p =
  begin
    (zero + n) * p
    ≡⟨⟩
    n * p
    ≡⟨⟩
    zero + n * p
    ≡⟨⟩
    zero * p + n * p
    ∎
*-distrib-r-+ (suc m) n p =
  begin
    (suc m + n) * p
    ≡⟨⟩
    suc (m + n) * p
    ≡⟨⟩
    p + (m + n) * p
    ≡⟨ cong (p +_) (*-distrib-r-+ m n p) ⟩
    p + (m * p + n * p)
    ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + m * p) + n * p
    ≡⟨⟩
    suc m * p + n * p
    ∎


*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p =
  begin
    (zero * n) * p
    ≡⟨⟩
    zero * p
    ≡⟨⟩
    zero
    ≡⟨⟩
    zero * (n * p)
    ∎
*-assoc (suc m) n p =
  begin
    (suc m * n) * p
    ≡⟨⟩
    (n + m * n) * p
    ≡⟨ *-distrib-r-+ n (m * n) p ⟩
    n * p + (m * n) * p
    ≡⟨ cong (n * p +_) (*-assoc m n p) ⟩
    n * p + m * (n * p)
    ≡⟨⟩
    suc m * (n * p)
    ∎

∸-0-n : ∀ (n : ℕ) → zero ∸ n ≡ zero
∸-0-n zero =
  begin
    zero ∸ zero
    ≡⟨⟩
    zero
    ∎
∸-0-n (suc n) =
  begin
     zero ∸ suc n
     ≡⟨⟩
     zero
     ∎

∸-+-assoc : ∀ (m n p : ℕ) → (m ∸ n) ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p =
  begin
    (zero ∸ n) ∸ p
    ≡⟨ cong (_∸ p) (∸-0-n n) ⟩
    zero ∸ p
    ≡⟨ ∸-0-n p ⟩
    zero
    ≡⟨ sym (∸-0-n (n + p)) ⟩
    zero ∸ (n + p)
    ∎
∸-+-assoc (suc m) zero p =
  begin
    (suc m ∸ zero) ∸ p
    ≡⟨⟩
    suc m ∸ p
    ≡⟨⟩
    suc m ∸ (zero + p)
    ∎
∸-+-assoc (suc m) (suc n) p =
  begin
    (suc m ∸ suc n) ∸ p
    ≡⟨⟩
    (m ∸ n) ∸ p
    ≡⟨ ∸-+-assoc m n p ⟩
    m ∸ (n + p)
    ≡⟨⟩
    suc m ∸ suc (n + p)
    ≡⟨⟩
    suc m ∸ (suc n + p)
    ∎

*-identity-l : ∀ (n : ℕ) → 1 * n ≡ n
*-identity-l zero = refl
*-identity-l (suc n) =
  begin
     1 * suc n
     ≡⟨⟩
     suc n + 0 * suc n
     ≡⟨⟩
     suc n + 0
     ≡⟨ cong suc (+-identity-r n) ⟩
     suc n
     ∎

*-absorb-r : ∀ (n : ℕ) → n * 0 ≡ 0
*-absorb-r zero = refl
*-absorb-r (suc n) =
  begin
    suc n * 0
    ≡⟨⟩
    0 + n * 0
    ≡⟨⟩
    n * 0
    ≡⟨ *-absorb-r n ⟩
    0
    ∎

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n =
  begin
    suc m * suc n
    ≡⟨⟩
    suc n + m * suc n
    ≡⟨⟩
    suc (n + m * suc n)
    ≡⟨ cong (λ k → suc (n + k)) (*-suc m n) ⟩
    suc (n + (m + m * n))
    ≡⟨ sym (cong suc (+-assoc n m (m * n))) ⟩
    suc ((n + m) + m * n)
    ≡⟨ cong (λ k → suc (k + m * n)) (+-comm n m) ⟩
    suc ((m + n) + m * n)
    ≡⟨ cong suc (+-assoc m n (m * n)) ⟩
    suc (m + (n + m * n))
    ≡⟨⟩
    suc m + suc m * n
    ∎

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n =
  begin
    zero * n
    ≡⟨⟩
    zero
    ≡⟨ sym (*-absorb-r n) ⟩
    n * zero ∎
*-comm (suc m) n =
  begin
    suc m * n
    ≡⟨⟩
    n + m * n
    ≡⟨ cong (n +_) (*-comm m n) ⟩
    n + n * m
    ≡⟨ sym (*-suc n m) ⟩
    n * suc m
    ∎

^-*-distrib-l-+ : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-*-distrib-l-+ m zero p =
  begin
    m ^ (zero + p)
    ≡⟨⟩
    m ^ p
    ≡⟨ sym (*-identity-l (m ^ p)) ⟩
    1 * (m ^ p)
    ≡⟨⟩
    (m ^ zero) * (m ^ p)
    ∎
^-*-distrib-l-+ m (suc n) p =
  begin
    m ^ (suc n + p)
    ≡⟨⟩
    m ^ suc (n + p)
    ≡⟨⟩
    m * (m ^ (n + p))
    ≡⟨ cong (m *_) (^-*-distrib-l-+ m n p) ⟩
    m * ((m ^ n) * (m ^ p))
    ≡⟨ sym (*-assoc m (m ^ n) (m ^ p)) ⟩
    (m * (m ^ n)) * (m ^ p)
    ≡⟨⟩
    (m ^ suc n) * (m ^ p)
    ∎

^-distrib-r-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distrib-r-* m n zero =
  begin
    (m * n) ^ zero
    ≡⟨⟩
    1
    ≡⟨⟩
    1 * 1
    ≡⟨⟩
    (m ^ zero) * (n ^ zero)
    ∎
^-distrib-r-* m n (suc p) =
  begin
    (m * n) ^ suc p
    ≡⟨⟩
    (m * n) * ((m * n) ^ p)
    ≡⟨ cong (m * n *_) (^-distrib-r-* m n p) ⟩
    (m * n) * ((m ^ p) * (n ^ p))
    ≡⟨ *-assoc m n ((m ^ p) * (n ^ p)) ⟩
    m * (n * ((m ^ p) * (n ^ p)))
    ≡⟨ sym (cong (m *_) (*-assoc n (m ^ p) (n ^ p))) ⟩
    m * ((n * (m ^ p)) * (n ^ p))
    ≡⟨ cong (λ k → m * (k * (n ^ p))) (*-comm n (m ^ p)) ⟩
    m * (((m ^ p) * n) * (n ^ p))
    ≡⟨ cong (m *_) (*-assoc (m ^ p) n (n ^ p)) ⟩
    m * ((m ^ p) * (n * (n ^ p)))
    ≡⟨ sym (*-assoc m (m ^ p) (n * (n ^ p))) ⟩
    (m * (m ^ p)) * (n * (n ^ p))
    ≡⟨⟩
    (m ^ suc p) * (n ^ suc p)
    ∎

^-^-distrib-l-* : ∀ (m n p : ℕ) → m ^ (n * p) ≡ (m ^ n) ^ p
^-^-distrib-l-* m n zero =
  begin
     m ^ (n * zero)
     ≡⟨ cong (m ^_) (*-absorb-r n) ⟩
     m ^ zero
     ≡⟨⟩
     1 ≡⟨⟩
     (m ^ n) ^ zero
     ∎
^-^-distrib-l-* m n (suc p) =
  begin
    m ^ (n * suc p)
    ≡⟨ cong (m ^_) (*-suc n p) ⟩
    m ^ (n + n * p)
    ≡⟨ ^-*-distrib-l-+ m n (n * p) ⟩
    (m ^ n) * (m ^ (n * p))
    ≡⟨ cong ((m ^ n) *_) (^-^-distrib-l-* m n p) ⟩
    (m ^ n) * ((m ^ n) ^ p)
    ≡⟨⟩
    (m ^ n) ^ suc p
    ∎

*-distrib-l-+ : ∀ (n p q : ℕ) → n * (p + q) ≡ n * p + n * q
*-distrib-l-+ n p q rewrite *-comm n (p + q) | *-comm n p | *-comm n q =
  *-distrib-r-+ p q n

suc-suc-2 : ∀ (n : ℕ) → 2 * suc n ≡ suc (suc (2 * n))
suc-suc-2 n =
  begin
    2 * suc n
    ≡⟨ *-suc 2 n ⟩
    2 + 2 * n
    ≡⟨⟩
    suc (1 + 2 * n)
    ≡⟨⟩
    suc (suc (0 + 2 * n))
    ≡⟨⟩
    suc (suc (2 * n))
    ∎
