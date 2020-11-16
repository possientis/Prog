open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; cong)


open import Data.Nat                     using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Empty                   using (⊥; ⊥-elim)
open import Relation.Nullary             using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable   using (True; toWitness)


