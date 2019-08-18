module list where

open import id
open import nat
open import bool
open import void
open import maybe

data 𝕃 {ℓ} (a : Set ℓ) : Set ℓ where
  []  : 𝕃 a
  _∷_ : a → 𝕃 a → 𝕃 a

infixr 5 _∷_

length :  ∀ {ℓ} {a : Set ℓ} → 𝕃 a → ℕ
length []       = 0
length (x ∷ xs) = succ (length xs)

_++_ : ∀ {ℓ} {a : Set ℓ} → 𝕃 a → 𝕃 a → 𝕃 a
[] ++ ys       = ys
(x ∷ xs) ++ ys = x ∷ xs ++ ys

infixr 6 _++_

++[] : ∀ {ℓ} → {a : Set ℓ} → (xs : 𝕃 a) → xs ++ [] ≡ xs
++[] []       = refl _
++[] (x ∷ xs) = ap ((λ l → x ∷ l)) (++[] xs)

++-[]-left : ∀ {ℓ} → {a : Set ℓ} → (xs ys : 𝕃 a) → xs ++ ys ≡ [] → xs ≡ []
++-[]-left [] _ _ = refl _

++-[]-right : ∀ {ℓ} → {a : Set ℓ} → (xs ys : 𝕃 a) → xs ++ ys ≡ [] → ys ≡ []
++-[]-right [] ys p = p

map : ∀ {ℓ ℓ'} {a : Set ℓ} {b : Set ℓ'} → (a → b) → 𝕃 a → 𝕃 b
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

map-[] : ∀ {ℓ ℓ'} → {a : Set ℓ} → {b : Set ℓ'} → (f : a -> b) → (xs : 𝕃 a) →
  map f xs ≡ [] → xs ≡ []
map-[] _ [] _ = refl _

filter : ∀ {ℓ} {a : Set ℓ} → (a → 𝔹) → 𝕃 a → 𝕃 a
filter p []       = []
filter p (x ∷ xs) = let ys = filter p xs in if p x then x ∷ ys else ys


remove : ∀ {ℓ} {a : Set ℓ} (eq : a → a → 𝔹) (x : a) → 𝕃 a → 𝕃 a
remove eq a xs = filter (λ x → not (eq a x)) xs

nth : ∀ {ℓ} {a : Set ℓ} → ℕ → 𝕃 a → maybe a
nth _ []              = nothing
nth zero (x ∷ _)      = just x
nth (succ n) (_ ∷ xs) = nth n xs

-- inefficient
sreverse : ∀ {ℓ} {a : Set ℓ} → 𝕃 a → 𝕃 a
sreverse []       = []
sreverse (x ∷ xs) = sreverse xs ++ (x ∷ [])

reverse-go : ∀ {ℓ} {a : Set ℓ} → 𝕃 a → 𝕃 a → 𝕃 a
reverse-go acc []       = acc
reverse-go acc (x ∷ xs) = reverse-go (x ∷ acc) xs

reverse : ∀ {ℓ} {a : Set ℓ} → 𝕃 a → 𝕃 a
reverse xs = reverse-go [] xs

{-
reverse_same : ∀ {ℓ} {a : Set ℓ} (xs : 𝕃 a) → sreverse xs ≡ reverse xs
reverse [] same     = refl []
reverse x ∷ xs same = {!!}
-}

length-++ : ∀ {ℓ} {a : Set ℓ} (xs ys : 𝕃 a) →
  length (xs ++ ys) ≡ length xs + length ys
  
length-++ [] ys       = refl (length ys)
length-++ (x ∷ xs) ys = ap succ (length-++ xs ys)

++-assoc : ∀ {ℓ} {a : Set ℓ} (xs ys zs : 𝕃 a) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs       = refl (ys ++ zs)
++-assoc (x ∷ xs) ys zs = ap (λ ls → x ∷ ls) (++-assoc xs ys zs)


length-filter : ∀ {ℓ} {a : Set ℓ} (p : a → 𝔹) (xs : 𝕃 a) →
  length (filter p xs) ≤ length xs
length-filter p []       = le-n 0
length-filter p (x ∷ xs) with (p x)
length-filter p (x ∷ xs) | tt = ≤-n-s (length-filter p xs)
length-filter p (x ∷ xs) | ff = le-s (length-filter p xs)

filter-idempotent : ∀ {ℓ} {a : Set ℓ} (p : a → 𝔹) (xs : 𝕃 a) →
  (filter p (filter p xs)) ≡ filter p xs
filter-idempotent p []            = refl []
filter-idempotent p (x ∷ xs) with inspect (p x)
filter-idempotent p (x ∷ xs) | tt with≡ eq =
  ≡-trans -- should be using rewrite, but don't understand it
    (ap (λ b → filter p (if b then x ∷ filter p xs else filter p xs)) eq)
    (≡-trans
      (ap (λ b → if b then x ∷ filter p (filter p xs) else filter p (filter p xs)) eq)
      (≡-sym
        (≡-trans
          (ap (λ b → if b then x ∷ filter p xs else filter p xs) eq)
          (ap (λ l → x ∷ l)
            (≡-sym (filter-idempotent p xs))))))
filter-idempotent p (x ∷ xs) | ff with≡ eq = ≡-trans
  ((ap (λ b → filter p (if b then x ∷ filter p xs else filter p xs)) eq ))
    (≡-sym
      (≡-trans
        ((ap (λ b → if b then x ∷ filter p xs else filter p xs) eq))
          (≡-sym (filter-idempotent p xs))))

length-reverse-go : ∀ {ℓ} {a : Set ℓ} (acc xs : 𝕃 a) →
  length (reverse-go acc xs) ≡ length acc + length xs
length-reverse-go acc []       = ≡-sym (+-n+O (length acc))
length-reverse-go acc (x ∷ xs) = ≡-trans
  (length-reverse-go (x ∷ acc) xs)
  (≡-sym (+-n+succ (length acc) (length xs)))

length-reverse : ∀ {ℓ} {a : Set ℓ} (xs : 𝕃 a) → length (reverse xs) ≡ length xs
length-reverse xs = length-reverse-go [] xs


concat : ∀ {ℓ} {a : Set ℓ} (xss : 𝕃 (𝕃 a)) → 𝕃 a
concat []           = []
concat (xs ∷ xss)   = xs ++ concat xss

