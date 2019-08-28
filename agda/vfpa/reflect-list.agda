module reflect-list where

open import id
open import bool
open import list
open import prod
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


empty-IsEmpty : ∀ {a : Set} → (r : 𝕄 a) → is-empty r ≡ tt → IsEmpty r
empty-IsEmpty (Inj []) p    = EmptyInj
empty-IsEmpty (App r1 r2) p = EmptyApp
  (empty-IsEmpty r1 (&&-left (is-empty r1) (is-empty r2) p))
  (empty-IsEmpty r2 (&&-right (is-empty r1) (is-empty r2) p))
empty-IsEmpty (Map x r) p   = EmptyMap (empty-IsEmpty r p)
empty-IsEmpty Nil p         = EmptyNil


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

data SmallStep {a : Set} : 𝕄 a → 𝕄 a → Set where
  SmallAppInj  : (xs : 𝕃 a) (r2 : 𝕄 a)
               → IsEmpty r2
               → SmallStep (App (Inj xs) r2) (Inj xs)
  SmallAppApp  : (r1 r2 r3 : 𝕄 a)
               → SmallStep (App (App r1 r2) r3) (App r1 (App r2 r3))
  SmallAppMap  : ∀ {a' : Set} (f : a' → a) (r1 : 𝕄 a') (r2 : 𝕄 a)
               → IsEmpty r2
               → SmallStep (App (Map f r1) r2) (Map f r1)
  SmallAppCons : {x : a} {r1 r2 : 𝕄 a}
               → SmallStep (App (Cons x r1) r2) (Cons x (App r1 r2))
  SmallAppNil  : {r2 : 𝕄 a} → SmallStep (App Nil r2) r2
  SmallMapInj  : ∀ {a' : Set} {f : a' → a} {xs : 𝕃 a'}
               →  SmallStep (Map f (Inj xs)) (Inj (map f xs))
  SmallMapApp  : ∀ {a' : Set} {f : a' → a} {r1 r2 : 𝕄 a'}
               →  SmallStep (Map f (App r1 r2)) (App (Map f r1) (Map f r2))
  SmallMapMap  : ∀ {a' a'' : Set} {f : a' → a} {g : a'' → a'} {r1 : 𝕄 a''}
               → SmallStep (Map f (Map g r1)) (Map (f ∘ g) r1)
  SmallMapCons : ∀ {a' : Set} {f : a' → a} {x : a'} {r1 : 𝕄 a'}
               → SmallStep (Map f (Cons x r1)) (Cons (f x) (Map f r1))
  SmallMapNil  : ∀ {a' : Set} {f : a' → a} → SmallStep (Map f Nil) Nil

{-
Small-small : ∀ {a : Set} {r1 r2 : 𝕄 a} → SmallStep r1 r2 → small-step r1 ≡ r2
Small-small (SmallAppInj xs r2 p) =
  ap (λ b → if b then Inj xs else App (Inj xs) r2) (IsEmpty-empty p)
Small-small (SmallAppApp r1 r2 r3) = refl _
Small-small (SmallAppMap f r1 r2 p) = {!!}
Small-small SmallAppCons = {!!}
Small-small SmallAppNil = {!!}
Small-small SmallMapInj = {!!}
Small-small SmallMapApp = {!!}
Small-small SmallMapMap = {!!}
Small-small SmallMapCons = {!!}
Small-small SmallMapNil = {!!}
-}
