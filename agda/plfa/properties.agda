open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; cong)

open import Data.String      using (String; _≟_) -- \?=
open import Data.Nat         using (ℕ; zero; suc)
open import Data.Empty       using (⊥; ⊥-elim)
open import Data.Product     using (_×_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Product     using () renaming (_,_ to ⟨_,_⟩)
open import Data.Sum         using (_⊎_; inj₁; inj₂)
open import Data.Bool        using (Bool; true; false)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Function         using (_∘_)

open import isomorphism

open import Lam.Id
open import Lam.Op
open import Lam.Type
open import Lam.Value
open import Lam.Typing
open import Lam.Syntax
open import Lam.Context
open import Lam.Progress
open import Lam.Canonical
open import Lam.Reduction

V¬—→ : ∀ {M N : Term}
  → Value M
    ---------------
  → ¬ (M —→ N)

V¬—→ (V-suc p) (ξ-suc q) = V¬—→ p q


—→¬V : ∀ {M N : Term}
  →  M —→ N
    ----------
  →  ¬ Value M

—→¬V p q = V¬—→ q p

-- a value which is well-typed in the empty context is canonical
canonical : ∀ {V : Term} {A : Type}
  → ∅ ⊢ V ∶ A
  → Value V
    ---------------
  → Canonical V ∶ A

canonical (⊢ƛ p) V-ƛ = C-ƛ p
canonical ⊢zero V-zero = C-zero
canonical (⊢suc p) (V-suc q) = C-suc (canonical p q)
canonical ⊢Num V-Num = C-Num
canonical ⊢Bool V-Bool = C-Bool

-- a canonical term is a value and is well-typed in the empty context
value : ∀ {M : Term} {A : Type}
  → Canonical M ∶ A
    --------------
  → Value M

value (C-ƛ x) = V-ƛ
value C-zero = V-zero
value (C-suc p) = V-suc (value p)
value C-Num = V-Num
value C-Bool = V-Bool


typed : ∀ {M : Term} {A : Type}
  → Canonical M ∶ A
    --------------------
  → ∅ ⊢ M ∶ A

typed (C-ƛ p) = ⊢ƛ p
typed C-zero = ⊢zero
typed (C-suc p) = ⊢suc (typed p)
typed C-Num = ⊢Num
typed C-Bool = ⊢Bool

progress : ∀ {M : Term} {A : Type}
  → ∅ ⊢ M ∶ A
    ----------
  → Progress M

progress (⊢ƛ p) = done V-ƛ
progress (⊢· p q) with (progress p)
... | step r = step (ξ-·₁ r)
... | done r with (progress q)
... | step s = step (ξ-·₂ r s)
progress (⊢· (⊢ƛ p) q) | done r | done s = step (β-ƛ s)
progress ⊢zero = {!!}
progress (⊢suc p) = {!!}
progress (⊢case p p₁ p₂) = {!!}
progress (⊢μ p) = {!!}
progress ⊢Num = {!!}
progress (⊢+ p p₁) = {!!}
progress (⊢* p p₁) = {!!}
progress ⊢Bool = {!!}
progress (⊢= p p₁) = {!!}
progress (⊢< p p₁) = {!!}
progress (⊢∧ p p₁) = {!!}
progress (⊢∨ p p₁) = {!!}
