open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
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

