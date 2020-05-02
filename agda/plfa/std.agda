open import Relation.Nullary using
  ( Dec
  ; yes
  ; no
  ; ¬_
  )

open import Relation.Nullary.Decidable using
  ( toWitness
  ; fromWitness
  ; ⌊_⌋
  )

open import Relation.Nullary.Negation using
  (¬?)

open import Relation.Nullary.Negation using
  (contraposition)

open import Relation.Nullary.Product using
  (_×-dec_)

open import Relation.Nullary.Sum using
  (_⊎-dec_)

open import Relation.Binary using
  (Decidable)

open import Data.Nat using
  ( ℕ
  ; zero
  ; suc
  ; _≤_
  ; _≤?_
  ; z≤n
  ; s≤s
  ; _+_
  ; _*_
  ; _∸_ --\.-
  )

open import Data.Nat.Properties using
  ( +-assoc
  ; +-suc
  ; +-comm
  ; ≤-refl     -- \<=, \le
  ; ≤-trans
  ; ≤-antisym
  ; ≤-total
  ; *-distribʳ-+
  )

open import Data.Bool using
  ( Bool
  ; true
  ; false
  ; T
  ; _∧_
  ; _∨_
  ; not
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

open import Data.Product using
  ( _×_
  ; _,_
  ; proj₁
  ; proj₂
  ; Σ
  ; ∃
  ; Σ-syntax
  ; ∃-syntax
  )

open import Data.Unit              using (⊤; tt)
open import Data.Sum               using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty             using (⊥; ⊥-elim)

open import Function               using (_∘_)
open import Function.Equivalence   using (_⇔_) -- less convenient than in isomorphism

open import Level                  using (Level)
