import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import isomorphism using (_≃_; ∀-extensionality)


∀-elim : ∀ {a : Set} {b : a → Set}
  → (L : ∀ (x : a) → b x)
  → (M : a)
    -------------------
  → b M

∀-elim L M = L M


∀-distrib-×-l : ∀ {a : Set} {p q : a → Set} →
  (∀ (x : a) → p x × q x) ≃ (∀ (x : a) → p x) × (∀ (x : a) → q x)

∀-distrib-×-l =  record
  { to = λ{f → ⟨ (λ{x → proj₁ (f x)}) , (λ{x → proj₂ (f x)}) ⟩}
  ; from = λ{⟨ f , g ⟩ → λ{x → ⟨ f x , g x ⟩}}
  ; from∘to = λ{f → ∀-extensionality (λ{x → refl})}
  ; to∘from = λ{⟨ f , g ⟩ → refl}
  }
