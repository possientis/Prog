open import nat
open import level

record Kripke : Set ℓ₁ where
  field W     : Set
  field R     : W → W → Set -- R x y : y is a possible future world of x
  field refl  : ∀ (x : W) → R x x
  field trans : ∀ {x y z : W} → R x y → R y z → R x z
  field V     : W → ℕ → Set -- V x n : n is true in world x
  field mono  : ∀ {x y : W} {n : ℕ} → R x y → V x n → V y n
  W' : Set  -- a record can contain definitions
  W' = W

f1 : Kripke → Set
f1 = Kripke.W    -- before record is open

open Kripke

f2 : Kripke → Set
f2 = W           -- after record is open

f3 : Kripke → Set
f3 = W'          -- record definition accessed like any other field


data world : Set where
  w0 : world
  w1 : world
  w2 : world

data rel : world -> world -> Set where
  rrefl : ∀ (w : world) → rel w w
  rel01 : rel w0 w1
  rel02 : rel w0 w2

rel-refl : ∀ (w : world) → rel w w
rel-refl = rrefl

rel-trans : ∀ {x y z : world} → rel x y → rel y z → rel x z
rel-trans (rrefl w) q = q
rel-trans rel01 (rrefl .w1) = rel01
rel-trans rel02 (rrefl .w2) = rel02

data val : world → ℕ → Set where
  v10 : val w1 0
  v11 : val w1 1
  v20 : val w2 0
  v21 : val w2 1

val-mono : ∀ {x y : world} {n : ℕ} → rel x y → val x n → val y n
val-mono (rrefl w) q = q

-- Example of Kripke structure
k : Kripke
k = record
  { W     = world
  ; R     = rel
  ; refl  = rel-refl
  ; trans = rel-trans
  ; V     = val
  ; mono  = val-mono
  }


