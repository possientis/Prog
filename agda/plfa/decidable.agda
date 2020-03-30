module decidable where

import Relation.Binary.PropositionalEquality as Eq

open        Eq                        using (_≡_; refl)
open import Data.Nat                  using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Sum                  using (_⊎_; inj₁; inj₂)
open import Data.Unit                 using (⊤; tt)
open import Data.Empty                using (⊥; ⊥-elim)
open import Data.Product              using (_×_; proj₁; proj₂)
open        Eq.≡-Reasoning            using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Relation.Nullary          using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import relations                 using (_<_; z<s; s<s)
open import isomorphism               using (_⇔_)

¬4≤2 : ¬ (4 ≤ 2)
¬4≤2 (s≤s (s≤s ()))

data Bool : Set where
  true  : Bool
  false : Bool

infix 4 _≤b_

_≤b_ : ℕ → ℕ → Bool
zero ≤b n = true
suc m ≤b zero = false
suc m ≤b suc n = m ≤b n

_ : (2 ≤b 4) ≡ true
_ =
  begin
    2 ≤b 4
    ≡⟨⟩
    1 ≤b 3
    ≡⟨⟩
    0 ≤b 2
    ≡⟨⟩
    true
    ∎

_ : (4 ≤b 2) ≡ false
_ =
  begin
    4 ≤b 2
    ≡⟨⟩
    3 ≤b 1
    ≡⟨⟩
    2 ≤b 0
    ≡⟨⟩
    false
    ∎


