open import relations

module braun {ℓ ℓ'} {a : Set ℓ}
  (_≤_     : a → a → Set ℓ')
  (≤-refl  : reflexive _≤_)
  (≤-anti  : antisymmetric _≤_)
  (≤-trans : transitive _≤_)
  where

open import id
open import nat

data braun-tree : (n : ℕ) → Set ℓ where
  bt-empty    : braun-tree 0
  bt-node-eq  : ∀ {n : ℕ} →
    a → braun-tree n → braun-tree n -> braun-tree (succ (n + n))
  bt-node-neq : ∀ {n : ℕ} →
    a → braun-tree (succ n) → braun-tree n → braun-tree (succ n + succ n)

length : ∀ {n : ℕ} → braun-tree n → ℕ
length bt-empty = 0
length (bt-node-eq x tl tr)  = succ (length tl + length tr)
length (bt-node-neq x tl tr) = succ (length tl + length tr)

length-from-type : {n : ℕ} → (t : braun-tree n) → length t ≡ n
length-from-type bt-empty              = refl 0
length-from-type (bt-node-eq {n} x tl tr)  =
  ap succ (≡-trans
    (ap (λ x → x + length tr) (length-from-type tl))
    (ap (λ x → n + x) (length-from-type tr)))
length-from-type (bt-node-neq {n} x tl tr) =
  ap succ (≡-trans
    (≡-trans {!!} (refl (succ n + n)))
    (≡-sym (+-n+succ n n)))
  
