module Lam.Stuck where

open import Data.Product     using (_×_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Product     using () renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Lam.Type
open import Lam.Value
open import Lam.Typing
open import Lam.Syntax
open import Lam.Normal
open import Lam.Context
open import Lam.Closure
open import Lam.Progress


Stuck : Term → Set
Stuck M = Normal M × ¬ Value M

unstuck : ∀ {M : Term} {A : Type}
  → ∅ ⊢ M ∶ A
    ----------
  → ¬ Stuck M

unstuck p q with progress p
unstuck p ⟨ q , r ⟩ | step s = q s
unstuck p ⟨ q , r ⟩ | done s = r s

-- Well typed terms don't get stuck
wttdgs : ∀ {M N : Term} {A : Type}
  →  ∅ ⊢ M ∶ A
  →  M —↠ N
    ----------
  → ¬ Stuck N

wttdgs p q r = {!!}
