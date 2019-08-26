module reflect-list where

open import id
open import bool
open import list
open import level
open import function

data 𝕄 : Set -> Set ℓ₁ where
  Inj  : {a : Set} → 𝕃 a → 𝕄 a
  App  : {a : Set} → 𝕄 a → 𝕄 a → 𝕄 a
  Map  : {a b : Set} → (a → b) → 𝕄 a → 𝕄 b
  Cons : {a : Set} → a → 𝕄 a → 𝕄 a
  Nil  : {a : Set} → 𝕄 a

𝕃⟦_⟧ : {a : Set} → 𝕄 a -> 𝕃 a
𝕃⟦ Inj xs ⟧   = xs
𝕃⟦ App r s ⟧  = 𝕃⟦ r ⟧ ++ 𝕃⟦ s ⟧
𝕃⟦ Map f r ⟧  = map f 𝕃⟦ r ⟧
𝕃⟦ Cons x r ⟧ = x ∷ 𝕃⟦ r ⟧
𝕃⟦ Nil ⟧      = []

-- A term is deemed empty based on syntax
is-empty : {a : Set} → 𝕄 a → 𝔹
is-empty (Inj [])      = tt
is-empty (Inj (_ ∷ _)) = ff
is-empty (App r1 r2)   = is-empty r1 && is-empty r2
is-empty (Map _ r)     = is-empty r
is-empty (Cons _ _)    = ff
is-empty Nil           = tt

data IsEmpty {a : Set} : 𝕄 a → Set where
  EmptyInj : IsEmpty (Inj [])
  EmptyApp : ∀ {r1 r2 : 𝕄 a} → IsEmpty r1 → IsEmpty r2 → IsEmpty (App r1 r2)
  EmptyMap : ∀ {a' : Set} {f : a' → a} {r : 𝕄 a'} → IsEmpty r -> IsEmpty (Map f r )
  EmptyNil : IsEmpty Nil

IsEmpty-empty : ∀ {a : Set} → {r : 𝕄 a} → (IsEmpty r) → is-empty r ≡ tt
IsEmpty-empty EmptyInj       = refl _
IsEmpty-empty (EmptyApp p q) = &&-and (IsEmpty-empty p) (IsEmpty-empty q)
IsEmpty-empty (EmptyMap p)   = IsEmpty-empty p
IsEmpty-empty EmptyNil       = refl _

{-
empty-IsEmpty : ∀ {a : Set} → (r : 𝕄 a) → is-empty r ≡ tt → IsEmpty r
empty-IsEmpty (Inj []) p    = EmptyInj
empty-IsEmpty (App r1 r2) p with (is-empty r1 , is-empty r2)
... | (b1, b2) = ?
empty-IsEmpty (Map x r) p = {!!}
empty-IsEmpty Nil p = {!!}
-}

-- If a term is deemed empty, then it denotes the empty list
is-empty-empty : ∀ {a : Set} → (r : 𝕄 a) → is-empty r ≡ tt -> 𝕃⟦ r ⟧ ≡ []
is-empty-empty (Inj []) _    = refl _
is-empty-empty (App r1 r2) p =
  ≡-trans
    (ap (λ x → x ++ 𝕃⟦ r2 ⟧)
      (is-empty-empty r1 (&&-left _ _ p)))
    (is-empty-empty r2 (&&-right _ _ p))
is-empty-empty (Map f r) p   = ap (map f) (is-empty-empty r p)
is-empty-empty Nil p         = refl _

-- If a term denotes the empty list, then it is deemed empty
empty-is-empty : ∀ {a : Set} → (r : 𝕄 a) → 𝕃⟦ r ⟧ ≡ [] → is-empty r ≡ tt
empty-is-empty (Inj []) p    = refl _
empty-is-empty (App r1 r2) p =
  ≡-trans
    (ap (λ x → x && is-empty r2)(empty-is-empty r1 (++-[]-left _ _ p)))
    (empty-is-empty r2 (++-[]-right _ _ p))
empty-is-empty (Map f r) p   = empty-is-empty r (map-[] _ _ p)
empty-is-empty Nil p         = refl _

-- one step transformation of redexes
small-step : {a : Set} → 𝕄 a → 𝕄 a
small-step (Inj xs)              = Inj xs    -- no reduction
small-step  Nil                  = Nil       -- no reduction
small-step (Cons x r)            = Cons x r  -- no reduction
-- small-step 'App'
small-step (App (Inj xs)     r2) = if is-empty r2 then Inj xs else App (Inj xs) r2
small-step (App (App r1 r1') r2) = App r1 (App r1' r2)
small-step (App (Map f r1)   r2) = if is-empty r2 then Map f r1 else App (Map f r1) r2
small-step (App (Cons x r1)  r2) = Cons x (App r1 r2)
small-step (App Nil          r2) = r2
-- small-step 'Map'
small-step (Map f (Inj xs))      = Inj (map f xs)
small-step (Map f (App r1 r2))   = App (Map f r1) (Map f r2)
small-step (Map f (Map g r))     = Map (f ∘ g) r
small-step (Map f (Cons x r))    = Cons (f x) (Map f r)
small-step (Map f Nil)           = Nil

