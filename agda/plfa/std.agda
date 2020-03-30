open import Data.Nat using
  ( ℕ
  ; zero
  ; suc
  ; _≤_
  ; z≤n
  ; s≤s
  )

open import Data.Nat.Properties using
  ( +-assoc
  ; +-suc
  ; +-comm
  ; ≤-refl     -- \<=, \le
  ; ≤-trans
  ; ≤-antisym
  ; ≤-total
  )

-- +-identity... cannot type superscript r with \^r, is this due to lean ?

import Relation.Binary.PropositionalEquality as Eq

open Eq using
  ( _≡_
  ; refl
  ; trans
  ; sym
  ; cong
  ; cong-app
  ; subst
  )

open Eq.≡-Reasoning using
  ( begin_
  ; _≡⟨⟩_
  ; _≡⟨_⟩_
  ; _∎
  )

import Data.Product using
  ( _×_
  ; _,_
  ; proj₁
  ; proj₂
  ; Σ
  ; ∃
  ; Σ-syntax
  ; ∃-syntax
  )

import Data.Unit                 using (⊤; tt)
import Data.Sum                  using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
import Data.Empty                using (⊥; ⊥-elim)

import Function                  using (_∘_)
import Function.Equivalence      using (_⇔_) -- less convenient than in isomorphism

import Relation.Nullary          using (¬_)
import Relation.Nullary.Negation using (contraposition)
