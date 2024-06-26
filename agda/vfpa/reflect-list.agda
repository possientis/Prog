module reflect-list where

open import id
open import nat
open import sum
open import func
open import bool
open import list
open import prod
open import level

-- syntax of 'list' language
data 𝕄 : Set -> Set ℓ₁ where
  Inj  : {a : Set} → 𝕃 a → 𝕄 a
  App  : {a : Set} → 𝕄 a → 𝕄 a → 𝕄 a
  Map  : {a b : Set} → (a → b) → 𝕄 a → 𝕄 b
  Cons : {a : Set} → a → 𝕄 a → 𝕄 a
  Nil  : {a : Set} → 𝕄 a

-- list semantics of 'list' language
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

-- predicate which expresses that a term is empty
data IsEmpty {a : Set} : 𝕄 a → Set where
  EmptyInj : IsEmpty (Inj [])
  EmptyApp : ∀ {r1 r2 : 𝕄 a} → IsEmpty r1 → IsEmpty r2 → IsEmpty (App r1 r2)
  EmptyMap : ∀ {a' : Set} {f : a' → a} {r : 𝕄 a'} → IsEmpty r -> IsEmpty (Map f r )
  EmptyNil : IsEmpty Nil

-- our predicate implies boolean function is true
IsEmpty-empty : ∀ {a : Set} → {r : 𝕄 a} → (IsEmpty r) → is-empty r ≡ tt
IsEmpty-empty EmptyInj       = refl _
IsEmpty-empty (EmptyApp p q) = &&-and (IsEmpty-empty p) (IsEmpty-empty q)
IsEmpty-empty (EmptyMap p)   = IsEmpty-empty p
IsEmpty-empty EmptyNil       = refl _

-- boolean function true implies our predicate
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

-- one step transformation of redexes as a function
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

-- one step transformation as a predicate
data SmallStep {a : Set} : 𝕄 a → 𝕄 a → Set where
  SmallAppInj  : (xs : 𝕃 a) (r2 : 𝕄 a)
               → IsEmpty r2
               → SmallStep (App (Inj xs) r2) (Inj xs)
  SmallAppApp  : (r1 r2 r3 : 𝕄 a)
               → SmallStep (App (App r1 r2) r3) (App r1 (App r2 r3))
  SmallAppMap  : ∀ {a' : Set} (f : a' → a) (r1 : 𝕄 a') (r2 : 𝕄 a)
               → IsEmpty r2
               → SmallStep (App (Map f r1) r2) (Map f r1)
  SmallAppCons : (x : a) (r1 r2 : 𝕄 a)
               → SmallStep (App (Cons x r1) r2) (Cons x (App r1 r2))
  SmallAppNil  : (r2 : 𝕄 a) → SmallStep (App Nil r2) r2
  SmallMapInj  : ∀ {a' : Set} (f : a' → a) (xs : 𝕃 a')
               →  SmallStep (Map f (Inj xs)) (Inj (map f xs))
  SmallMapApp  : ∀ {a' : Set} (f : a' → a) (r1 r2 : 𝕄 a')
               →  SmallStep (Map f (App r1 r2)) (App (Map f r1) (Map f r2))
  SmallMapMap  : ∀ {a' a'' : Set} (f : a' → a) (g : a'' → a') (r1 : 𝕄 a'')
               → SmallStep (Map f (Map g r1)) (Map (f ∘ g) r1)
  SmallMapCons : ∀ {a' : Set} (f : a' → a) (x : a') (r1 : 𝕄 a')
               → SmallStep (Map f (Cons x r1)) (Cons (f x) (Map f r1))
  SmallMapNil  : ∀ {a' : Set} (f : a' → a) → SmallStep (Map f Nil) Nil

-- precicate implies function 
Small-small : ∀ {a : Set} {r1 r2 : 𝕄 a} → SmallStep r1 r2 → small-step r1 ≡ r2
Small-small (SmallAppInj xs r2 p)   =
  ap (λ b → if b then Inj xs else App (Inj xs) r2) (IsEmpty-empty p)
Small-small (SmallAppApp r1 r2 r3)  = refl _
Small-small (SmallAppMap f r1 r2 p) =
  ap (λ b → if b then Map f r1 else App (Map f r1) r2) (IsEmpty-empty p)
Small-small (SmallAppCons x r1 r2)  = refl _
Small-small (SmallAppNil r2)        = refl _
Small-small (SmallMapInj f xs)      = refl _
Small-small (SmallMapApp f r1 r2)   = refl _
Small-small (SmallMapMap f g r1)    = ap (λ h → Map h r1) (refl _)
Small-small (SmallMapCons f x r1)   = refl _
Small-small (SmallMapNil f)         = refl _

-- function implies no reduction or predicate
small-Small
  : ∀ {a : Set} (r1 r2 : 𝕄 a)
  → small-step r1 ≡ r2
  → (r1 ≡ r2) ∨ SmallStep r1 r2

small-Small (Inj x) r2 p                 = left p
small-Small (App (Inj xs) r2) r3 p with 𝔹-dec (is-empty r2) tt
small-Small (App (Inj xs) r2) r3 p | left q  = right
  (cast
    (ap (λ r → SmallStep (App (Inj xs) r2) r)
      (≡-trans
        (ap (λ b → if b then Inj xs else App (Inj xs) r2) (≡-sym q))
        p))
    (SmallAppInj xs r2 (empty-IsEmpty r2 q)))
small-Small (App (Inj x) r2) r3 p | right q = left
  (≡-trans
    (ap (λ b → if b then Inj x else App (Inj x) r2)(≡-sym (not-tt-ff _ q)))
    p)
small-Small (App (App r1 r4) r2) r3 p = right (
  cast
    (ap (λ r → SmallStep (App (App r1 r4) r2) r) p)
    (SmallAppApp r1 r4 r2))
small-Small (App (Map f r1) r2) r3 p with 𝔹-dec (is-empty r2) tt
small-Small (App (Map f r1) r2) r3 p | left  q = right
  (cast
    (ap
      (λ r → SmallStep (App (Map f r1) r2) r)
      (≡-trans
        (ap (λ b → if b then Map f r1 else App (Map f r1) r2) (≡-sym q))
        p))
    (SmallAppMap f r1 r2 (empty-IsEmpty r2 q)))
small-Small (App (Map f r1) r2) r3 p | right q = left
  (≡-trans
    (ap
      (λ b → if b then Map f r1 else App (Map f r1) r2)
      (≡-sym (not-tt-ff (is-empty r2) q)))
    p)
small-Small (App (Cons x r1) r2) r3 p = right
  (cast
    (ap
      (λ r → SmallStep (App (Cons x r1) r2) r)
      p)
    (SmallAppCons x r1 r2))
small-Small (App Nil r2) r3 p = right
  (cast
    (ap (λ r → SmallStep (App Nil r2) r) p)
    (SmallAppNil r2))
small-Small (Map f (Inj xs)) r2 p = right
  (cast
    (ap (λ r → SmallStep (Map f (Inj xs)) r) p)
    (SmallMapInj f xs))
small-Small (Map f (App r1 r2)) r3 p = right
  (cast (ap (λ r → SmallStep (Map f (App r1 r2)) r) p)
  (SmallMapApp f r1 r2))
small-Small (Map f (Map g r1)) r2 p = right
  (cast
    (ap (λ r → SmallStep (Map f (Map g r1)) r) p)
    (SmallMapMap f g r1))
small-Small (Map f (Cons x r1)) r2 p = right
  (cast
    (ap (λ r → SmallStep (Map f (Cons x r1)) r) p)
    (SmallMapCons f x r1))
small-Small (Map f Nil) r2 p = right
  (cast
    (ap (λ r → SmallStep (Map f Nil) r) p)
    (SmallMapNil f))
small-Small (Cons x r1) r2 p = left p
small-Small Nil r2 p = left p

superdev : {a : Set} → 𝕄 a → 𝕄 a
superdev (Inj x)     = Inj x
superdev (App r1 r2) = small-step (App (superdev r1) (superdev r2))
superdev (Map f r1)  = small-step (Map f (superdev r1))
superdev (Cons x r1) = small-step (Cons x (superdev r1))
superdev Nil         = Nil

simplify : {a : Set} → ℕ → 𝕄 a → 𝕄 a
simplify zero     r = r
simplify (succ n) r = superdev (simplify n r)


-- small-step preserves semantics
small-step-sound : ∀ {a : Set} → (r : 𝕄 a) → 𝕃⟦ small-step r ⟧ ≡ 𝕃⟦ r ⟧
small-step-sound (Inj xs)          = refl _
small-step-sound (App (Inj xs) r2) with 𝔹-dec (is-empty r2) tt
small-step-sound (App (Inj xs) r2) | left p  =
  ≡-trans
    (ap (λ b → 𝕃⟦ if b then Inj xs else App (Inj xs) r2 ⟧) p)
    (≡-sym (≡-trans (ap (λ l → xs ++ l) (is-empty-empty r2 p))(++[] xs)))
small-step-sound (App (Inj xs) r2) | right p =
  ≡-trans
    (ap (λ b → 𝕃⟦ if b then Inj xs else App (Inj xs) r2 ⟧)
      (not-tt-ff (is-empty r2) p))
    (refl _)
small-step-sound (App (App r1 r3) r2) = ≡-sym (++-assoc 𝕃⟦ r1 ⟧ 𝕃⟦ r3 ⟧ 𝕃⟦ r2 ⟧)
small-step-sound (App (Map f r1) r2)  with 𝔹-dec (is-empty r2) tt
small-step-sound (App (Map f r1) r2) | left p  =
  ≡-trans
    (ap (λ b → 𝕃⟦ if b then Map f r1 else App (Map f r1) r2 ⟧) p)
    (≡-sym (≡-trans
      (ap (λ l → map f 𝕃⟦ r1 ⟧ ++ l) (is-empty-empty r2 p))
      (++[] (map f 𝕃⟦ r1 ⟧ ))))
small-step-sound (App (Map f r1) r2) | right p =
   ≡-trans
     (ap (λ b → 𝕃⟦ if b then Map f r1 else App (Map f r1) r2 ⟧)
       (not-tt-ff (is-empty r2) p))
     (refl _)
small-step-sound (App (Cons x r1) r2) = refl _
small-step-sound (App Nil r2)         = refl _
small-step-sound (Map f (Inj x))      = refl _
small-step-sound (Map f (App r1 r2))  = ≡-sym (++-map f 𝕃⟦ r1 ⟧ 𝕃⟦ r2 ⟧)
small-step-sound (Map f (Map g r1))   = ++-∘ g f 𝕃⟦ r1 ⟧
small-step-sound (Map f (Cons x r1))  = refl _
small-step-sound (Map f Nil)          = refl _
small-step-sound (Cons x r)           = refl _
small-step-sound Nil                  = refl _

-- superdev preserves semantics
superdev-sound : ∀ {a : Set} → (r : 𝕄 a) → 𝕃⟦ superdev r ⟧ ≡ 𝕃⟦ r ⟧
superdev-sound (Inj xs)    = refl _
superdev-sound (App r1 r2) = ≡-trans
  (small-step-sound (App (superdev r1)(superdev r2)))
  (≡-trans
    (ap (λ l → l ++ 𝕃⟦ superdev r2 ⟧) (superdev-sound r1))
    (ap (λ l → 𝕃⟦ r1 ⟧ ++ l) (superdev-sound r2)))
superdev-sound (Map f r1)  = ≡-trans
  (small-step-sound (Map f (superdev r1)))
  (ap (map f) (superdev-sound r1))
superdev-sound (Cons x r1) = ap (λ l → x ∷ l) (superdev-sound r1)
superdev-sound Nil         = refl _

-- simplify preserves semantics
simplify-sound : ∀ {a : Set} → (n : ℕ) → (r : 𝕄 a) → 𝕃⟦ simplify n r ⟧ ≡ 𝕃⟦ r ⟧
simplify-sound zero r     = refl _
simplify-sound (succ n) r = ≡-trans
  (superdev-sound (simplify n r))
  (simplify-sound n r)


