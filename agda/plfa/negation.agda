open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)
open import isomorphism using (_≃_; extensionality)


¬_ : Set → Set
¬ x = x → ⊥


¬-elim : ∀ {a : Set}
  → ¬ a
  →   a
    -----
  →   ⊥

¬-elim ¬x x = ¬x x

infix 3 ¬_ -- binds more tightly than ⊎ and ×, but less than everything else

¬¬-intro : ∀ {a : Set}
  →   a
    -----
  →  ¬ ¬ a

¬¬-intro x = λ{¬x → ¬x x}

¬¬-intro' : ∀ {a : Set}
  →   a
    -----
  →  ¬ ¬ a

¬¬-intro' x ¬x = ¬x x

¬¬¬-elim : ∀ {a : Set}
  →   ¬ ¬ ¬ a
     ---------
  →    ¬ a

¬¬¬-elim ¬¬¬x x = ¬¬¬x (¬¬-intro x)

contraposition : ∀ {a b : Set}
  →     (a → b)
     -------------
  →   (¬ b → ¬ a)

contraposition a→b ¬b x = ¬b (a→b x)

_≢_ : ∀ {a : Set} → a → a → Set
x ≢ y = ¬ x ≡ y

ex1 : 1 ≢ 2
ex1 ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ ()

id : ⊥ → ⊥
id x = x

id' : ⊥ → ⊥
id' ()

id≡id' : id ≡ id'
id≡id' = extensionality (λ ())

-- Two proofs of a negation are equal
assimilation : ∀ {a : Set} (¬x ¬x' : ¬ a) → ¬x ≡ ¬x'
assimilation ¬x ¬x' = extensionality λ{x → ⊥-elim (¬x x)}

irreflexivity : ∀ (n : ℕ) → ¬ (n < n)
irreflexivity (suc n) (s≤s p) = irreflexivity n p
