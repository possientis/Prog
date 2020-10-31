module Lam.Normal where


open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Lam.Syntax
open import Lam.Reduction

Normal : Term -> Set
Normal M = ∀ {N : Term} → ¬ (M —→ N)
