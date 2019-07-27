open import relations

module braun {ℓ ℓ'} {a : Set ℓ}
  (_≤_     : a → a → Set ℓ')
  (≤-refl  : reflexive _≤_)
  (≤-anti  : antisymmetric _≤_)
  (≤-trans : transitive _≤_)
  where

open import id
open import nat
open import sum

data braun-tree : (n : ℕ) → Set ℓ where
  bt-empty    : braun-tree 0
  bt-node-eq  : ∀ {n : ℕ} →
    a → braun-tree n → braun-tree n -> braun-tree (succ (n + n))
  bt-node-neq : ∀ {n : ℕ} →
    a → braun-tree (succ n) → braun-tree n → braun-tree (succ n + succ n)

size : ∀ {n : ℕ} → braun-tree n → ℕ
size bt-empty = 0
size (bt-node-eq x tl tr)  = succ (size tl + size tr)
size (bt-node-neq x tl tr) = succ (size tl + size tr)

size-from-type : {n : ℕ} → (t : braun-tree n) → size t ≡ n
size-from-type bt-empty              = refl 0
size-from-type (bt-node-eq {n} x tl tr)  =
  ap succ (≡-trans
    (ap (λ x → x + size tr) (size-from-type tl))
    (ap (λ x → n + x) (size-from-type tr)))
size-from-type (bt-node-neq {n} x tl tr) =
  ap succ (≡-trans
    (≡-trans
      (≡-trans
        (ap (λ x → x + size tr) (size-from-type tl))
        (ap succ (ap (λ x → n + x) (size-from-type tr))))
      (refl (succ n + n)))
    (≡-sym (+-n+succ n n)))
  
join : {n m : ℕ} → ((n ≡ m) ∨ (n ≡ succ m)) →
  a → braun-tree n → braun-tree m → braun-tree (succ (n + m))
join {n} {m} (left  p) x tl tr = cast {!!} (bt-node-eq x tl (cast {!!} tr))
join (right p) x tl tr = {!!}
