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

import Relation.Binary.PropositionalEquality.Core as Eq

open import Relation.Binary.PropositionalEquality.Core using
  ( _≡_
  ; refl
  ; trans
  ; sym
  ; cong
  ; subst
  )


open Eq.≡-Reasoning using
  ( begin_
  ; _≡⟨⟩_
  ; _∎
  ; step-≡
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

open import Data.List using
  ( List
  ; _++_
  ; length
  ; reverse
  ; map
  ; foldr
  ; downFrom
  )

open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Properties using
  ( reverse-++-commute
  ; map-compose
  ; map-++-commute
  ; foldr-++
  ; mapIsFold
  )

open import Algebra.Structures using (IsMonoid)
open import Relation.Unary using (Decidable)
open import Relation.Binary using (Decidable)
