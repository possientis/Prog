open import Data.Nat using (_≤_; z≤n; s≤s)
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
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

import Function using (_∘_)
