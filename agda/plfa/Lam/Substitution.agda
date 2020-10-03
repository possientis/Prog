module Lam.Substitution where

open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; subst;cong)

open import Data.Empty       using (⊥; ⊥-elim)
open import Data.String      using (_≟_) -- \?=
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Lam.Id
open import Lam.Type
open import Lam.Subst
open import Lam.Typing
open import Lam.Syntax
open import Lam.Context

substitution : ∀ {Γ : Context} {x : Id} {N V : Term} {A B : Type}
  → ∅ ⊢ V ∶ A
  → Γ , x ∶ A ⊢ N ∶ B
    --------------------
  → Γ ⊢ N [ x := V ] ∶ B

substitution {Γ} {x} p (⊢` {x = y} q) with y ≟ x
substitution {Γ} {x} p (⊢` {x = _} Z) | yes r = weaken p
substitution {Γ} {x} p (⊢` {x = _} (S q r)) | yes s = ⊥-elim (q s)
substitution {Γ} {x} p (⊢` {x = _} Z) | no r = ⊢` (⊥-elim (r refl))
substitution {Γ} {x} p (⊢` {x = _} (S q r)) | no s = ⊢` r
substitution {Γ} {x} p (⊢ƛ {x = y} q) with y ≟ x
... | yes refl = ⊢ƛ (drop q)
... | no r  = ⊢ƛ (substitution p (swap r q))
substitution {Γ} {x} p (⊢· q r) = ⊢· (substitution p q) (substitution p r)
substitution {Γ} {x} p ⊢zero = ⊢zero
substitution {Γ} {x} p (⊢suc q) = ⊢suc (substitution p q)
substitution {Γ} {x} p (⊢case {x = y} q r s) with y ≟ x
... | yes refl = ⊢case (substitution p q) (substitution p r) (drop s)
... | no t  = ⊢case (substitution p q) (substitution p r) (substitution p (swap t s))
substitution {Γ} {x} p (⊢if q r s) = ⊢if
  (substitution p q) (substitution p r) (substitution p s)
substitution {Γ} {x} p (⊢μ {x = y} q) with y ≟ x
... | yes refl = ⊢μ (drop q)
... | no r  = ⊢μ (substitution p (swap r q))
substitution {Γ} {x} p ⊢Num = ⊢Num
substitution {Γ} {x} p (⊢+ q r) = ⊢+ (substitution p q) (substitution p r)
substitution {Γ} {x} p (⊢* q r) = ⊢* (substitution p q) (substitution p r)
substitution {Γ} {x} p ⊢Bool = ⊢Bool
substitution {Γ} {x} p (⊢= q r) = ⊢= (substitution p q) (substitution p r)
substitution {Γ} {x} p (⊢< q r) = ⊢< (substitution p q) (substitution p r)
substitution {Γ} {x} p (⊢∧ q r) = ⊢∧ (substitution p q) (substitution p r)
substitution {Γ} {x} p (⊢∨ q r) = ⊢∨ (substitution p q) (substitution p r)
